// Lean compiler output
// Module: Lean.Elab.PreDefinition.TerminationHint
// Imports: public import Lean.Parser.Term meta import Lean.Parser.Term import Init.Omega
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
static const lean_array_object l_Lean_Elab_instInhabitedTerminationBy_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_instInhabitedTerminationBy_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedTerminationBy_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instInhabitedTerminationBy_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_instInhabitedTerminationBy_default___closed__1 = (const lean_object*)&l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedTerminationBy_default = (const lean_object*)&l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedTerminationBy = (const lean_object*)&l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value;
static const lean_ctor_object l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedDecreasingBy_default = (const lean_object*)&l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedDecreasingBy = (const lean_object*)&l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedPartialFixpointType_default;
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedPartialFixpointType;
static const lean_ctor_object l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedPartialFixpoint_default = (const lean_object*)&l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedPartialFixpoint = (const lean_object*)&l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 8, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_instInhabitedTerminationHints_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedTerminationHints_default = (const lean_object*)&l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedTerminationHints = (const lean_object*)&l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_isInductiveFixpoint(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_isInductiveFixpoint___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isCoinductiveFixpoint(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_isCoinductiveFixpoint___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isPartialFixpoint(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_isPartialFixpoint___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isLatticeTheoretic(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_isLatticeTheoretic___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Lean_Elab_TerminationHints_none = (const lean_object*)&l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_TerminationHints_ensureNone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unused termination hints, function is "};
static const lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__0 = (const lean_object*)&l_Lean_Elab_TerminationHints_ensureNone___closed__0_value;
static lean_once_cell_t l_Lean_Elab_TerminationHints_ensureNone___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__1;
static const lean_string_object l_Lean_Elab_TerminationHints_ensureNone___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "unused `partial_fixpoint`, function is "};
static const lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__2 = (const lean_object*)&l_Lean_Elab_TerminationHints_ensureNone___closed__2_value;
static lean_once_cell_t l_Lean_Elab_TerminationHints_ensureNone___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__3;
static const lean_string_object l_Lean_Elab_TerminationHints_ensureNone___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "unused `coinductive_fixpoint`, function is "};
static const lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__4 = (const lean_object*)&l_Lean_Elab_TerminationHints_ensureNone___closed__4_value;
static lean_once_cell_t l_Lean_Elab_TerminationHints_ensureNone___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__5;
static const lean_string_object l_Lean_Elab_TerminationHints_ensureNone___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "unused `inductive_fixpoint`, function is "};
static const lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__6 = (const lean_object*)&l_Lean_Elab_TerminationHints_ensureNone___closed__6_value;
static lean_once_cell_t l_Lean_Elab_TerminationHints_ensureNone___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__7;
static const lean_string_object l_Lean_Elab_TerminationHints_ensureNone___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "unused `decreasing_by`, function is "};
static const lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__8 = (const lean_object*)&l_Lean_Elab_TerminationHints_ensureNone___closed__8_value;
static lean_once_cell_t l_Lean_Elab_TerminationHints_ensureNone___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__9;
static const lean_string_object l_Lean_Elab_TerminationHints_ensureNone___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "unused `termination_by`, function is "};
static const lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__10 = (const lean_object*)&l_Lean_Elab_TerminationHints_ensureNone___closed__10_value;
static lean_once_cell_t l_Lean_Elab_TerminationHints_ensureNone___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__11;
static const lean_string_object l_Lean_Elab_TerminationHints_ensureNone___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unused `termination_by\?`, function is "};
static const lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__12 = (const lean_object*)&l_Lean_Elab_TerminationHints_ensureNone___closed__12_value;
static lean_once_cell_t l_Lean_Elab_TerminationHints_ensureNone___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationHints_ensureNone___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_TerminationHints_isNotNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_isNotNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " parameters"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "one parameter"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_TerminationBy_checkVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = " bound in `termination_by`, but the body of "};
static const lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__0 = (const lean_object*)&l_Lean_Elab_TerminationBy_checkVars___closed__0_value;
static lean_once_cell_t l_Lean_Elab_TerminationBy_checkVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__1;
static const lean_string_object l_Lean_Elab_TerminationBy_checkVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " only binds "};
static const lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__2 = (const lean_object*)&l_Lean_Elab_TerminationBy_checkVars___closed__2_value;
static lean_once_cell_t l_Lean_Elab_TerminationBy_checkVars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__3;
static const lean_string_object l_Lean_Elab_TerminationBy_checkVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__4 = (const lean_object*)&l_Lean_Elab_TerminationBy_checkVars___closed__4_value;
static lean_once_cell_t l_Lean_Elab_TerminationBy_checkVars___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__5;
static const lean_string_object l_Lean_Elab_TerminationBy_checkVars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__6 = (const lean_object*)&l_Lean_Elab_TerminationBy_checkVars___closed__6_value;
static const lean_ctor_object l_Lean_Elab_TerminationBy_checkVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_TerminationBy_checkVars___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__7 = (const lean_object*)&l_Lean_Elab_TerminationBy_checkVars___closed__7_value;
static const lean_string_object l_Lean_Elab_TerminationBy_checkVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = " (Since Lean v4.6.0, the `termination_by` clause no longer "};
static const lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__8 = (const lean_object*)&l_Lean_Elab_TerminationBy_checkVars___closed__8_value;
static lean_once_cell_t l_Lean_Elab_TerminationBy_checkVars___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__9;
static const lean_string_object l_Lean_Elab_TerminationBy_checkVars___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "expects the function name here.)"};
static const lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__10 = (const lean_object*)&l_Lean_Elab_TerminationBy_checkVars___closed__10_value;
static const lean_ctor_object l_Lean_Elab_TerminationBy_checkVars___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TerminationBy_checkVars___closed__10_value)}};
static const lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__11 = (const lean_object*)&l_Lean_Elab_TerminationBy_checkVars___closed__11_value;
static lean_once_cell_t l_Lean_Elab_TerminationBy_checkVars___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationBy_checkVars___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "decreasingBy"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unexpected `decreasing_by` syntax"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "partialFixpoint"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "coinductiveFixpoint"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "inductiveFixpoint"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "terminationBy"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "terminationBy\?"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "unexpected `termination_by` syntax"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2_value;
static lean_once_cell_t l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "no extra parameters bounds, please omit the `=>`"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4_value;
static lean_once_cell_t l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__4_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Unexpected Termination.suffix syntax: "};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__5_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " of kind "};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__6_value;
static const lean_closure_object l_Lean_Elab_elabTerminationHints___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_elabTerminationHints___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 143, 0, 201, 195, 223, 93, 180)}};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 199, 246, 58, 76, 113, 58, 46)}};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorIdx___impl(uint8_t v_x_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_box(v_x_13_);
v___x_15_ = lean_obj_tag_nat(v___x_14_);
lean_dec(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorIdx___impl___boxed(lean_object* v_x_16_){
_start:
{
uint8_t v_x_4__boxed_17_; lean_object* v_res_18_; 
v_x_4__boxed_17_ = lean_unbox(v_x_16_);
v_res_18_ = l_Lean_Elab_PartialFixpointType_ctorIdx___impl(v_x_4__boxed_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___redArg(lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___redArg___boxed(lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Elab_PartialFixpointType_ctorElim___redArg(v_k_20_);
lean_dec(v_k_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, uint8_t v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
lean_inc(v_k_26_);
return v_k_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___boxed(lean_object* v_motive_27_, lean_object* v_ctorIdx_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
uint8_t v_t_boxed_32_; lean_object* v_res_33_; 
v_t_boxed_32_ = lean_unbox(v_t_29_);
v_res_33_ = l_Lean_Elab_PartialFixpointType_ctorElim(v_motive_27_, v_ctorIdx_28_, v_t_boxed_32_, v_h_30_, v_k_31_);
lean_dec(v_k_31_);
lean_dec(v_ctorIdx_28_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(lean_object* v_partialFixpoint_34_){
_start:
{
lean_inc(v_partialFixpoint_34_);
return v_partialFixpoint_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg___boxed(lean_object* v_partialFixpoint_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(v_partialFixpoint_35_);
lean_dec(v_partialFixpoint_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(lean_object* v_motive_37_, uint8_t v_t_38_, lean_object* v_h_39_, lean_object* v_partialFixpoint_40_){
_start:
{
lean_inc(v_partialFixpoint_40_);
return v_partialFixpoint_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___boxed(lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_partialFixpoint_44_){
_start:
{
uint8_t v_t_boxed_45_; lean_object* v_res_46_; 
v_t_boxed_45_ = lean_unbox(v_t_42_);
v_res_46_ = l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(v_motive_41_, v_t_boxed_45_, v_h_43_, v_partialFixpoint_44_);
lean_dec(v_partialFixpoint_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(lean_object* v_coinductiveFixpoint_47_){
_start:
{
lean_inc(v_coinductiveFixpoint_47_);
return v_coinductiveFixpoint_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg___boxed(lean_object* v_coinductiveFixpoint_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(v_coinductiveFixpoint_48_);
lean_dec(v_coinductiveFixpoint_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(lean_object* v_motive_50_, uint8_t v_t_51_, lean_object* v_h_52_, lean_object* v_coinductiveFixpoint_53_){
_start:
{
lean_inc(v_coinductiveFixpoint_53_);
return v_coinductiveFixpoint_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___boxed(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_coinductiveFixpoint_57_){
_start:
{
uint8_t v_t_boxed_58_; lean_object* v_res_59_; 
v_t_boxed_58_ = lean_unbox(v_t_55_);
v_res_59_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(v_motive_54_, v_t_boxed_58_, v_h_56_, v_coinductiveFixpoint_57_);
lean_dec(v_coinductiveFixpoint_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(lean_object* v_inductiveFixpoint_60_){
_start:
{
lean_inc(v_inductiveFixpoint_60_);
return v_inductiveFixpoint_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg___boxed(lean_object* v_inductiveFixpoint_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(v_inductiveFixpoint_61_);
lean_dec(v_inductiveFixpoint_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(lean_object* v_motive_63_, uint8_t v_t_64_, lean_object* v_h_65_, lean_object* v_inductiveFixpoint_66_){
_start:
{
lean_inc(v_inductiveFixpoint_66_);
return v_inductiveFixpoint_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___boxed(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_inductiveFixpoint_70_){
_start:
{
uint8_t v_t_boxed_71_; lean_object* v_res_72_; 
v_t_boxed_71_ = lean_unbox(v_t_68_);
v_res_72_ = l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(v_motive_67_, v_t_boxed_71_, v_h_69_, v_inductiveFixpoint_70_);
lean_dec(v_inductiveFixpoint_70_);
return v_res_72_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedPartialFixpointType_default(void){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedPartialFixpointType(void){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = 0;
return v___x_74_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isInductiveFixpoint(uint8_t v_x_88_){
_start:
{
if (v_x_88_ == 2)
{
uint8_t v___x_89_; 
v___x_89_ = 1;
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isInductiveFixpoint___boxed(lean_object* v_x_91_){
_start:
{
uint8_t v_x_17__boxed_92_; uint8_t v_res_93_; lean_object* v_r_94_; 
v_x_17__boxed_92_ = lean_unbox(v_x_91_);
v_res_93_ = l_Lean_Elab_isInductiveFixpoint(v_x_17__boxed_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isCoinductiveFixpoint(uint8_t v_x_95_){
_start:
{
if (v_x_95_ == 1)
{
uint8_t v___x_96_; 
v___x_96_ = 1;
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isCoinductiveFixpoint___boxed(lean_object* v_x_98_){
_start:
{
uint8_t v_x_17__boxed_99_; uint8_t v_res_100_; lean_object* v_r_101_; 
v_x_17__boxed_99_ = lean_unbox(v_x_98_);
v_res_100_ = l_Lean_Elab_isCoinductiveFixpoint(v_x_17__boxed_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isPartialFixpoint(uint8_t v_x_102_){
_start:
{
if (v_x_102_ == 0)
{
uint8_t v___x_103_; 
v___x_103_ = 1;
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isPartialFixpoint___boxed(lean_object* v_x_105_){
_start:
{
uint8_t v_x_17__boxed_106_; uint8_t v_res_107_; lean_object* v_r_108_; 
v_x_17__boxed_106_ = lean_unbox(v_x_105_);
v_res_107_ = l_Lean_Elab_isPartialFixpoint(v_x_17__boxed_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isLatticeTheoretic(uint8_t v_p_109_){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = l_Lean_Elab_isInductiveFixpoint(v_p_109_);
if (v___x_110_ == 0)
{
uint8_t v___x_111_; 
v___x_111_ = l_Lean_Elab_isCoinductiveFixpoint(v_p_109_);
return v___x_111_;
}
else
{
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isLatticeTheoretic___boxed(lean_object* v_p_112_){
_start:
{
uint8_t v_p_boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_p_boxed_113_ = lean_unbox(v_p_112_);
v_res_114_ = l_Lean_Elab_isLatticeTheoretic(v_p_boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_117_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_121_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
lean_ctor_set(v___x_123_, 2, v___x_122_);
lean_ctor_set(v___x_123_, 3, v___x_122_);
lean_ctor_set(v___x_123_, 4, v___x_121_);
lean_ctor_set(v___x_123_, 5, v___x_121_);
lean_ctor_set(v___x_123_, 6, v___x_121_);
lean_ctor_set(v___x_123_, 7, v___x_121_);
lean_ctor_set(v___x_123_, 8, v___x_121_);
lean_ctor_set(v___x_123_, 9, v___x_121_);
lean_ctor_set(v___x_123_, 10, v___x_121_);
lean_ctor_set(v___x_123_, 11, v___x_120_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_unsigned_to_nat(32u);
v___x_125_ = lean_mk_empty_array_with_capacity(v___x_124_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_127_ = ((size_t)5ULL);
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_unsigned_to_nat(32u);
v___x_130_ = lean_mk_empty_array_with_capacity(v___x_129_);
v___x_131_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3);
v___x_132_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
lean_ctor_set(v___x_132_, 2, v___x_128_);
lean_ctor_set(v___x_132_, 3, v___x_128_);
lean_ctor_set_usize(v___x_132_, 4, v___x_127_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = lean_box(1);
v___x_134_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4);
v___x_135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
v___x_136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_133_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(lean_object* v_msgData_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___x_141_; lean_object* v_toCold_142_; lean_object* v_env_143_; lean_object* v_options_144_; uint8_t v___x_145_; lean_object* v_env_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_141_ = lean_st_ref_get(v___y_139_);
v_toCold_142_ = lean_ctor_get(v___y_138_, 0);
v_env_143_ = lean_ctor_get(v___x_141_, 0);
lean_inc_ref(v_env_143_);
lean_dec(v___x_141_);
v_options_144_ = lean_ctor_get(v_toCold_142_, 2);
v___x_145_ = 0;
v_env_146_ = l_Lean_Environment_setRecordingDeps(v_env_143_, v___x_145_);
v___x_147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2);
v___x_148_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_144_);
v___x_149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_149_, 0, v_env_146_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
lean_ctor_set(v___x_149_, 2, v___x_148_);
lean_ctor_set(v___x_149_, 3, v_options_144_);
v___x_150_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_msgData_137_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v_msgData_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_156_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_165_, uint8_t v___y_166_, lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 1)
{
lean_object* v_pre_168_; 
v_pre_168_ = lean_ctor_get(v_x_167_, 0);
switch(lean_obj_tag(v_pre_168_))
{
case 1:
{
lean_object* v_pre_169_; 
v_pre_169_ = lean_ctor_get(v_pre_168_, 0);
switch(lean_obj_tag(v_pre_169_))
{
case 0:
{
lean_object* v_str_170_; lean_object* v_str_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_str_170_ = lean_ctor_get(v_x_167_, 1);
v_str_171_ = lean_ctor_get(v_pre_168_, 1);
v___x_172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0));
v___x_173_ = lean_string_dec_eq(v_str_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1));
v___x_175_ = lean_string_dec_eq(v_str_171_, v___x_174_);
if (v___x_175_ == 0)
{
return v___x_175_;
}
else
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2));
v___x_177_ = lean_string_dec_eq(v_str_170_, v___x_176_);
if (v___x_177_ == 0)
{
return v___x_177_;
}
else
{
return v_suppressElabErrors_165_;
}
}
}
else
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3));
v___x_179_ = lean_string_dec_eq(v_str_170_, v___x_178_);
if (v___x_179_ == 0)
{
return v___x_179_;
}
else
{
return v_suppressElabErrors_165_;
}
}
}
case 1:
{
lean_object* v_pre_180_; 
v_pre_180_ = lean_ctor_get(v_pre_169_, 0);
if (lean_obj_tag(v_pre_180_) == 0)
{
lean_object* v_str_181_; lean_object* v_str_182_; lean_object* v_str_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_str_181_ = lean_ctor_get(v_x_167_, 1);
v_str_182_ = lean_ctor_get(v_pre_168_, 1);
v_str_183_ = lean_ctor_get(v_pre_169_, 1);
v___x_184_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4));
v___x_185_ = lean_string_dec_eq(v_str_183_, v___x_184_);
if (v___x_185_ == 0)
{
return v___x_185_;
}
else
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5));
v___x_187_ = lean_string_dec_eq(v_str_182_, v___x_186_);
if (v___x_187_ == 0)
{
return v___x_187_;
}
else
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6));
v___x_189_ = lean_string_dec_eq(v_str_181_, v___x_188_);
if (v___x_189_ == 0)
{
return v___x_189_;
}
else
{
return v_suppressElabErrors_165_;
}
}
}
}
else
{
return v___y_166_;
}
}
default: 
{
return v___y_166_;
}
}
}
case 0:
{
lean_object* v_str_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_str_190_ = lean_ctor_get(v_x_167_, 1);
v___x_191_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7));
v___x_192_ = lean_string_dec_eq(v_str_190_, v___x_191_);
if (v___x_192_ == 0)
{
return v___x_192_;
}
else
{
return v_suppressElabErrors_165_;
}
}
default: 
{
return v___y_166_;
}
}
}
else
{
return v___y_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_193_, lean_object* v___y_194_, lean_object* v_x_195_){
_start:
{
uint8_t v_suppressElabErrors_boxed_196_; uint8_t v___y_3406__boxed_197_; uint8_t v_res_198_; lean_object* v_r_199_; 
v_suppressElabErrors_boxed_196_ = lean_unbox(v_suppressElabErrors_193_);
v___y_3406__boxed_197_ = lean_unbox(v___y_194_);
v_res_198_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_196_, v___y_3406__boxed_197_, v_x_195_);
lean_dec(v_x_195_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(lean_object* v_opts_200_, lean_object* v_opt_201_){
_start:
{
lean_object* v_name_202_; lean_object* v_defValue_203_; lean_object* v_map_204_; lean_object* v___x_205_; 
v_name_202_ = lean_ctor_get(v_opt_201_, 0);
v_defValue_203_ = lean_ctor_get(v_opt_201_, 1);
v_map_204_ = lean_ctor_get(v_opts_200_, 0);
v___x_205_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_204_, v_name_202_);
if (lean_obj_tag(v___x_205_) == 0)
{
uint8_t v___x_206_; 
v___x_206_ = lean_unbox(v_defValue_203_);
return v___x_206_;
}
else
{
lean_object* v_val_207_; 
v_val_207_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v___x_205_, 1);
if (lean_obj_tag(v_val_207_) == 1)
{
uint8_t v_v_208_; 
v_v_208_ = lean_ctor_get_uint8(v_val_207_, 0);
lean_dec_ref_known(v_val_207_, 0);
return v_v_208_;
}
else
{
uint8_t v___x_209_; 
lean_dec(v_val_207_);
v___x_209_ = lean_unbox(v_defValue_203_);
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_210_, lean_object* v_opt_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_opts_210_, v_opt_211_);
lean_dec_ref(v_opt_211_);
lean_dec_ref(v_opts_210_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(lean_object* v_ref_215_, lean_object* v_msgData_216_, uint8_t v_severity_217_, uint8_t v_isSilent_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___y_223_; uint8_t v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; uint8_t v___y_228_; lean_object* v___y_229_; lean_object* v_toCold_230_; lean_object* v___y_231_; lean_object* v___y_260_; lean_object* v___y_261_; uint8_t v___y_262_; uint8_t v___y_263_; lean_object* v___y_264_; uint8_t v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; uint8_t v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; uint8_t v___y_291_; uint8_t v___y_292_; lean_object* v___y_293_; uint8_t v___y_297_; uint8_t v___y_298_; uint8_t v___y_299_; uint8_t v___x_310_; uint8_t v___y_312_; uint8_t v___y_313_; uint8_t v___y_314_; uint8_t v___y_316_; uint8_t v___x_324_; 
v___x_310_ = 2;
v___x_324_ = l_Lean_instBEqMessageSeverity_beq(v_severity_217_, v___x_310_);
if (v___x_324_ == 0)
{
v___y_316_ = v___x_324_;
goto v___jp_315_;
}
else
{
uint8_t v___x_325_; 
lean_inc_ref(v_msgData_216_);
v___x_325_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_216_);
v___y_316_ = v___x_325_;
goto v___jp_315_;
}
v___jp_222_:
{
lean_object* v_currNamespace_232_; lean_object* v_openDecls_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v_env_238_; lean_object* v_nextMacroScope_239_; lean_object* v_ngen_240_; lean_object* v_auxDeclNGen_241_; lean_object* v_traceState_242_; lean_object* v_cache_243_; lean_object* v_recordedDeps_244_; lean_object* v_messages_245_; lean_object* v_infoState_246_; lean_object* v_snapshotTasks_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_258_; 
v_currNamespace_232_ = lean_ctor_get(v_toCold_230_, 4);
v_openDecls_233_ = lean_ctor_get(v_toCold_230_, 5);
lean_inc(v_openDecls_233_);
lean_inc(v_currNamespace_232_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v_currNamespace_232_);
lean_ctor_set(v___x_234_, 1, v_openDecls_233_);
v___x_235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___y_223_);
lean_inc_ref(v___y_226_);
lean_inc_ref(v___y_229_);
v___x_236_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_236_, 0, v___y_229_);
lean_ctor_set(v___x_236_, 1, v___y_227_);
lean_ctor_set(v___x_236_, 2, v___y_225_);
lean_ctor_set(v___x_236_, 3, v___y_226_);
lean_ctor_set(v___x_236_, 4, v___x_235_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*5, v___y_228_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*5 + 1, v___y_224_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*5 + 2, v_isSilent_218_);
v___x_237_ = lean_st_ref_take(v___y_231_);
v_env_238_ = lean_ctor_get(v___x_237_, 0);
v_nextMacroScope_239_ = lean_ctor_get(v___x_237_, 1);
v_ngen_240_ = lean_ctor_get(v___x_237_, 2);
v_auxDeclNGen_241_ = lean_ctor_get(v___x_237_, 3);
v_traceState_242_ = lean_ctor_get(v___x_237_, 4);
v_cache_243_ = lean_ctor_get(v___x_237_, 5);
v_recordedDeps_244_ = lean_ctor_get(v___x_237_, 6);
v_messages_245_ = lean_ctor_get(v___x_237_, 7);
v_infoState_246_ = lean_ctor_get(v___x_237_, 8);
v_snapshotTasks_247_ = lean_ctor_get(v___x_237_, 9);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_258_ == 0)
{
v___x_249_ = v___x_237_;
v_isShared_250_ = v_isSharedCheck_258_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_snapshotTasks_247_);
lean_inc(v_infoState_246_);
lean_inc(v_messages_245_);
lean_inc(v_recordedDeps_244_);
lean_inc(v_cache_243_);
lean_inc(v_traceState_242_);
lean_inc(v_auxDeclNGen_241_);
lean_inc(v_ngen_240_);
lean_inc(v_nextMacroScope_239_);
lean_inc(v_env_238_);
lean_dec(v___x_237_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_258_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_251_ = lean_box(0);
v___x_252_ = l_Lean_MessageLog_add(v___x_236_, v_messages_245_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 7, v___x_252_);
v___x_254_ = v___x_249_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_env_238_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_nextMacroScope_239_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_ngen_240_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v_auxDeclNGen_241_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v_traceState_242_);
lean_ctor_set(v_reuseFailAlloc_257_, 5, v_cache_243_);
lean_ctor_set(v_reuseFailAlloc_257_, 6, v_recordedDeps_244_);
lean_ctor_set(v_reuseFailAlloc_257_, 7, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_257_, 8, v_infoState_246_);
lean_ctor_set(v_reuseFailAlloc_257_, 9, v_snapshotTasks_247_);
v___x_254_ = v_reuseFailAlloc_257_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_st_ref_put(v___y_231_, v___x_254_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_251_);
return v___x_256_;
}
}
}
v___jp_259_:
{
lean_object* v_fileName_268_; lean_object* v_fileMap_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_285_; 
v_fileName_268_ = lean_ctor_get(v___y_266_, 0);
v_fileMap_269_ = lean_ctor_get(v___y_266_, 1);
v___x_270_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_216_);
v___x_271_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v___x_270_, v___y_219_, v___y_220_);
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_285_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_285_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_285_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
lean_inc_ref_n(v_fileMap_269_, 2);
v___x_276_ = l_Lean_FileMap_toPosition(v_fileMap_269_, v___y_264_);
lean_dec(v___y_264_);
v___x_277_ = l_Lean_FileMap_toPosition(v_fileMap_269_, v___y_267_);
lean_dec(v___y_267_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
v___x_279_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0));
if (v___y_262_ == 0)
{
lean_del_object(v___x_274_);
lean_dec_ref(v___y_260_);
v___y_223_ = v_a_272_;
v___y_224_ = v___y_263_;
v___y_225_ = v___x_278_;
v___y_226_ = v___x_279_;
v___y_227_ = v___x_276_;
v___y_228_ = v___y_265_;
v___y_229_ = v_fileName_268_;
v_toCold_230_ = v___y_261_;
v___y_231_ = v___y_220_;
goto v___jp_222_;
}
else
{
uint8_t v___x_280_; 
lean_inc(v_a_272_);
v___x_280_ = l_Lean_MessageData_hasTag(v___y_260_, v_a_272_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_283_; 
lean_dec_ref_known(v___x_278_, 1);
lean_dec_ref(v___x_276_);
lean_dec(v_a_272_);
v___x_281_ = lean_box(0);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_281_);
v___x_283_ = v___x_274_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
else
{
lean_del_object(v___x_274_);
v___y_223_ = v_a_272_;
v___y_224_ = v___y_263_;
v___y_225_ = v___x_278_;
v___y_226_ = v___x_279_;
v___y_227_ = v___x_276_;
v___y_228_ = v___y_265_;
v___y_229_ = v_fileName_268_;
v_toCold_230_ = v___y_261_;
v___y_231_ = v___y_220_;
goto v___jp_222_;
}
}
}
}
v___jp_286_:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Syntax_getTailPos_x3f(v___y_290_, v___y_292_);
lean_dec(v___y_290_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_inc(v___y_293_);
v___y_260_ = v___y_288_;
v___y_261_ = v___y_289_;
v___y_262_ = v___y_287_;
v___y_263_ = v___y_291_;
v___y_264_ = v___y_293_;
v___y_265_ = v___y_292_;
v___y_266_ = v___y_289_;
v___y_267_ = v___y_293_;
goto v___jp_259_;
}
else
{
lean_object* v_val_295_; 
v_val_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_val_295_);
lean_dec_ref_known(v___x_294_, 1);
v___y_260_ = v___y_288_;
v___y_261_ = v___y_289_;
v___y_262_ = v___y_287_;
v___y_263_ = v___y_291_;
v___y_264_ = v___y_293_;
v___y_265_ = v___y_292_;
v___y_266_ = v___y_289_;
v___y_267_ = v_val_295_;
goto v___jp_259_;
}
}
v___jp_296_:
{
lean_object* v_toCold_300_; lean_object* v_ref_301_; uint8_t v_suppressElabErrors_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___f_305_; lean_object* v_ref_306_; lean_object* v___x_307_; 
v_toCold_300_ = lean_ctor_get(v___y_219_, 0);
v_ref_301_ = lean_ctor_get(v___y_219_, 2);
v_suppressElabErrors_302_ = lean_ctor_get_uint8(v___y_219_, sizeof(void*)*3 + 2);
v___x_303_ = lean_box(v_suppressElabErrors_302_);
v___x_304_ = lean_box(v___y_297_);
v___f_305_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_305_, 0, v___x_303_);
lean_closure_set(v___f_305_, 1, v___x_304_);
v_ref_306_ = l_Lean_replaceRef(v_ref_215_, v_ref_301_);
v___x_307_ = l_Lean_Syntax_getPos_x3f(v_ref_306_, v___y_298_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___y_287_ = v_suppressElabErrors_302_;
v___y_288_ = v___f_305_;
v___y_289_ = v_toCold_300_;
v___y_290_ = v_ref_306_;
v___y_291_ = v___y_299_;
v___y_292_ = v___y_298_;
v___y_293_ = v___x_308_;
goto v___jp_286_;
}
else
{
lean_object* v_val_309_; 
v_val_309_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_val_309_);
lean_dec_ref_known(v___x_307_, 1);
v___y_287_ = v_suppressElabErrors_302_;
v___y_288_ = v___f_305_;
v___y_289_ = v_toCold_300_;
v___y_290_ = v_ref_306_;
v___y_291_ = v___y_299_;
v___y_292_ = v___y_298_;
v___y_293_ = v_val_309_;
goto v___jp_286_;
}
}
v___jp_311_:
{
if (v___y_314_ == 0)
{
v___y_297_ = v___y_312_;
v___y_298_ = v___y_313_;
v___y_299_ = v_severity_217_;
goto v___jp_296_;
}
else
{
v___y_297_ = v___y_312_;
v___y_298_ = v___y_313_;
v___y_299_ = v___x_310_;
goto v___jp_296_;
}
}
v___jp_315_:
{
if (v___y_316_ == 0)
{
uint8_t v___x_317_; uint8_t v___x_318_; 
v___x_317_ = 1;
v___x_318_ = l_Lean_instBEqMessageSeverity_beq(v_severity_217_, v___x_317_);
if (v___x_318_ == 0)
{
v___y_312_ = v___y_316_;
v___y_313_ = v___y_316_;
v___y_314_ = v___x_318_;
goto v___jp_311_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_319_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_219_);
v___x_320_ = l_Lean_warningAsError;
v___x_321_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v___x_319_, v___x_320_);
lean_dec_ref(v___x_319_);
v___y_312_ = v___y_316_;
v___y_313_ = v___y_316_;
v___y_314_ = v___x_321_;
goto v___jp_311_;
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref(v_msgData_216_);
v___x_322_ = lean_box(0);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___boxed(lean_object* v_ref_326_, lean_object* v_msgData_327_, lean_object* v_severity_328_, lean_object* v_isSilent_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
uint8_t v_severity_boxed_333_; uint8_t v_isSilent_boxed_334_; lean_object* v_res_335_; 
v_severity_boxed_333_ = lean_unbox(v_severity_328_);
v_isSilent_boxed_334_ = lean_unbox(v_isSilent_329_);
v_res_335_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_326_, v_msgData_327_, v_severity_boxed_333_, v_isSilent_boxed_334_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v_ref_326_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(lean_object* v_ref_336_, lean_object* v_msgData_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
uint8_t v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; 
v___x_341_ = 1;
v___x_342_ = 0;
v___x_343_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_336_, v_msgData_337_, v___x_341_, v___x_342_, v___y_338_, v___y_339_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(lean_object* v_ref_344_, lean_object* v_msgData_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_344_, v_msgData_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v_ref_344_);
return v_res_349_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__0));
v___x_352_ = l_Lean_stringToMessageData(v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__2));
v___x_355_ = l_Lean_stringToMessageData(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__4));
v___x_358_ = l_Lean_stringToMessageData(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__6));
v___x_361_ = l_Lean_stringToMessageData(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__8));
v___x_364_ = l_Lean_stringToMessageData(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__10));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__12));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone(lean_object* v_hints_371_, lean_object* v_reason_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_ref_376_; lean_object* v_terminationBy_x3f_x3f_377_; lean_object* v_terminationBy_x3f_378_; lean_object* v_partialFixpoint_x3f_379_; lean_object* v_decreasingBy_x3f_380_; uint8_t v_warnIfRedundant_381_; lean_object* v___y_383_; lean_object* v___y_384_; 
v_ref_376_ = lean_ctor_get(v_hints_371_, 0);
lean_inc(v_ref_376_);
v_terminationBy_x3f_x3f_377_ = lean_ctor_get(v_hints_371_, 1);
lean_inc(v_terminationBy_x3f_x3f_377_);
v_terminationBy_x3f_378_ = lean_ctor_get(v_hints_371_, 2);
lean_inc(v_terminationBy_x3f_378_);
v_partialFixpoint_x3f_379_ = lean_ctor_get(v_hints_371_, 3);
lean_inc(v_partialFixpoint_x3f_379_);
v_decreasingBy_x3f_380_ = lean_ctor_get(v_hints_371_, 4);
lean_inc(v_decreasingBy_x3f_380_);
v_warnIfRedundant_381_ = lean_ctor_get_uint8(v_hints_371_, sizeof(void*)*6);
lean_dec_ref(v_hints_371_);
if (v_warnIfRedundant_381_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_decreasingBy_x3f_380_);
lean_dec(v_partialFixpoint_x3f_379_);
lean_dec(v_terminationBy_x3f_378_);
lean_dec(v_terminationBy_x3f_x3f_377_);
lean_dec(v_ref_376_);
lean_dec_ref(v_reason_372_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_x3f_377_) == 0)
{
if (lean_obj_tag(v_terminationBy_x3f_378_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_380_) == 0)
{
lean_dec(v_ref_376_);
if (lean_obj_tag(v_partialFixpoint_x3f_379_) == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec_ref(v_reason_372_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
else
{
lean_object* v_val_393_; uint8_t v_fixpointType_394_; 
v_val_393_ = lean_ctor_get(v_partialFixpoint_x3f_379_, 0);
lean_inc(v_val_393_);
lean_dec_ref_known(v_partialFixpoint_x3f_379_, 1);
v_fixpointType_394_ = lean_ctor_get_uint8(v_val_393_, sizeof(void*)*2);
switch(v_fixpointType_394_)
{
case 0:
{
lean_object* v_ref_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_ref_395_ = lean_ctor_get(v_val_393_, 0);
lean_inc(v_ref_395_);
lean_dec(v_val_393_);
v___x_396_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__3, &l_Lean_Elab_TerminationHints_ensureNone___closed__3_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3);
v___x_397_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_395_, v___x_398_, v_a_373_, v_a_374_);
lean_dec(v_ref_395_);
return v___x_399_;
}
case 1:
{
lean_object* v_ref_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_ref_400_ = lean_ctor_get(v_val_393_, 0);
lean_inc(v_ref_400_);
lean_dec(v_val_393_);
v___x_401_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__5, &l_Lean_Elab_TerminationHints_ensureNone___closed__5_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5);
v___x_402_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_400_, v___x_403_, v_a_373_, v_a_374_);
lean_dec(v_ref_400_);
return v___x_404_;
}
default: 
{
lean_object* v_ref_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_ref_405_ = lean_ctor_get(v_val_393_, 0);
lean_inc(v_ref_405_);
lean_dec(v_val_393_);
v___x_406_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__7, &l_Lean_Elab_TerminationHints_ensureNone___closed__7_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7);
v___x_407_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_405_, v___x_408_, v_a_373_, v_a_374_);
lean_dec(v_ref_405_);
return v___x_409_;
}
}
}
}
else
{
if (lean_obj_tag(v_partialFixpoint_x3f_379_) == 0)
{
lean_object* v_val_410_; lean_object* v_ref_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_ref_376_);
v_val_410_ = lean_ctor_get(v_decreasingBy_x3f_380_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v_decreasingBy_x3f_380_, 1);
v_ref_411_ = lean_ctor_get(v_val_410_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_val_410_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v_val_410_, 1);
lean_dec(v_unused_422_);
v___x_413_ = v_val_410_;
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_ref_411_);
lean_dec(v_val_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_415_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__9, &l_Lean_Elab_TerminationHints_ensureNone___closed__9_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9);
v___x_416_ = l_Lean_stringToMessageData(v_reason_372_);
if (v_isShared_414_ == 0)
{
lean_ctor_set_tag(v___x_413_, 7);
lean_ctor_set(v___x_413_, 1, v___x_416_);
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_418_ = v___x_413_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___x_416_);
v___x_418_ = v_reuseFailAlloc_420_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_411_, v___x_418_, v_a_373_, v_a_374_);
lean_dec(v_ref_411_);
return v___x_419_;
}
}
}
else
{
lean_dec_ref_known(v_decreasingBy_x3f_380_, 1);
lean_dec(v_partialFixpoint_x3f_379_);
v___y_383_ = v_a_373_;
v___y_384_ = v_a_374_;
goto v___jp_382_;
}
}
}
else
{
if (lean_obj_tag(v_decreasingBy_x3f_380_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_379_) == 0)
{
lean_object* v_val_423_; lean_object* v_ref_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_ref_376_);
v_val_423_ = lean_ctor_get(v_terminationBy_x3f_378_, 0);
lean_inc(v_val_423_);
lean_dec_ref_known(v_terminationBy_x3f_378_, 1);
v_ref_424_ = lean_ctor_get(v_val_423_, 0);
lean_inc(v_ref_424_);
lean_dec(v_val_423_);
v___x_425_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__11, &l_Lean_Elab_TerminationHints_ensureNone___closed__11_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11);
v___x_426_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_424_, v___x_427_, v_a_373_, v_a_374_);
lean_dec(v_ref_424_);
return v___x_428_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_378_, 1);
lean_dec(v_partialFixpoint_x3f_379_);
v___y_383_ = v_a_373_;
v___y_384_ = v_a_374_;
goto v___jp_382_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_378_, 1);
lean_dec(v_decreasingBy_x3f_380_);
lean_dec(v_partialFixpoint_x3f_379_);
v___y_383_ = v_a_373_;
v___y_384_ = v_a_374_;
goto v___jp_382_;
}
}
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_378_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_380_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_379_) == 0)
{
lean_object* v_val_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec(v_ref_376_);
v_val_429_ = lean_ctor_get(v_terminationBy_x3f_x3f_377_, 0);
lean_inc(v_val_429_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_377_, 1);
v___x_430_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__13, &l_Lean_Elab_TerminationHints_ensureNone___closed__13_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13);
v___x_431_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_val_429_, v___x_432_, v_a_373_, v_a_374_);
lean_dec(v_val_429_);
return v___x_433_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_377_, 1);
lean_dec(v_partialFixpoint_x3f_379_);
v___y_383_ = v_a_373_;
v___y_384_ = v_a_374_;
goto v___jp_382_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_377_, 1);
lean_dec(v_decreasingBy_x3f_380_);
lean_dec(v_partialFixpoint_x3f_379_);
v___y_383_ = v_a_373_;
v___y_384_ = v_a_374_;
goto v___jp_382_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_377_, 1);
lean_dec(v_decreasingBy_x3f_380_);
lean_dec(v_partialFixpoint_x3f_379_);
lean_dec(v_terminationBy_x3f_378_);
v___y_383_ = v_a_373_;
v___y_384_ = v_a_374_;
goto v___jp_382_;
}
}
}
v___jp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__1, &l_Lean_Elab_TerminationHints_ensureNone___closed__1_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1);
v___x_386_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_376_, v___x_387_, v___y_383_, v___y_384_);
lean_dec(v_ref_376_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone___boxed(lean_object* v_hints_434_, lean_object* v_reason_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Elab_TerminationHints_ensureNone(v_hints_434_, v_reason_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_439_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_TerminationHints_isNotNone(lean_object* v_hints_440_){
_start:
{
lean_object* v_terminationBy_x3f_x3f_441_; 
v_terminationBy_x3f_x3f_441_ = lean_ctor_get(v_hints_440_, 1);
if (lean_obj_tag(v_terminationBy_x3f_x3f_441_) == 0)
{
lean_object* v_terminationBy_x3f_442_; 
v_terminationBy_x3f_442_ = lean_ctor_get(v_hints_440_, 2);
if (lean_obj_tag(v_terminationBy_x3f_442_) == 0)
{
lean_object* v_decreasingBy_x3f_443_; 
v_decreasingBy_x3f_443_ = lean_ctor_get(v_hints_440_, 4);
if (lean_obj_tag(v_decreasingBy_x3f_443_) == 0)
{
lean_object* v_partialFixpoint_x3f_444_; 
v_partialFixpoint_x3f_444_ = lean_ctor_get(v_hints_440_, 3);
if (lean_obj_tag(v_partialFixpoint_x3f_444_) == 0)
{
uint8_t v___x_445_; 
v___x_445_ = 0;
return v___x_445_;
}
else
{
uint8_t v___x_446_; 
v___x_446_ = 1;
return v___x_446_;
}
}
else
{
uint8_t v___x_447_; 
v___x_447_ = 1;
return v___x_447_;
}
}
else
{
uint8_t v___x_448_; 
v___x_448_ = 1;
return v___x_448_;
}
}
else
{
uint8_t v___x_449_; 
v___x_449_ = 1;
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_isNotNone___boxed(lean_object* v_hints_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_Lean_Elab_TerminationHints_isNotNone(v_hints_450_);
lean_dec_ref(v_hints_450_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object* v_headerParams_453_, lean_object* v_hints_454_, lean_object* v_value_455_){
_start:
{
lean_object* v_ref_456_; lean_object* v_terminationBy_x3f_x3f_457_; lean_object* v_terminationBy_x3f_458_; lean_object* v_partialFixpoint_x3f_459_; lean_object* v_decreasingBy_x3f_460_; uint8_t v_warnIfRedundant_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_470_; 
v_ref_456_ = lean_ctor_get(v_hints_454_, 0);
v_terminationBy_x3f_x3f_457_ = lean_ctor_get(v_hints_454_, 1);
v_terminationBy_x3f_458_ = lean_ctor_get(v_hints_454_, 2);
v_partialFixpoint_x3f_459_ = lean_ctor_get(v_hints_454_, 3);
v_decreasingBy_x3f_460_ = lean_ctor_get(v_hints_454_, 4);
v_warnIfRedundant_461_ = lean_ctor_get_uint8(v_hints_454_, sizeof(void*)*6);
v_isSharedCheck_470_ = !lean_is_exclusive(v_hints_454_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v_hints_454_, 5);
lean_dec(v_unused_471_);
v___x_463_ = v_hints_454_;
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_decreasingBy_x3f_460_);
lean_inc(v_partialFixpoint_x3f_459_);
lean_inc(v_terminationBy_x3f_458_);
lean_inc(v_terminationBy_x3f_x3f_457_);
lean_inc(v_ref_456_);
lean_dec(v_hints_454_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_465_ = l_Lean_Expr_getNumHeadLambdas(v_value_455_);
v___x_466_ = lean_nat_sub(v___x_465_, v_headerParams_453_);
lean_dec(v___x_465_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 5, v___x_466_);
v___x_468_ = v___x_463_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_ref_456_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_terminationBy_x3f_x3f_457_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_terminationBy_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_partialFixpoint_x3f_459_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v_decreasingBy_x3f_460_);
lean_ctor_set(v_reuseFailAlloc_469_, 5, v___x_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, sizeof(void*)*6, v_warnIfRedundant_461_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(lean_object* v_headerParams_472_, lean_object* v_hints_473_, lean_object* v_value_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v_headerParams_472_, v_hints_473_, v_value_474_);
lean_dec_ref(v_value_474_);
lean_dec(v_headerParams_472_);
return v_res_475_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3));
v___x_483_ = l_Lean_MessageData_ofFormat(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(lean_object* v_a_484_){
_start:
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_dec_eq(v_a_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_487_ = l_Nat_reprFast(v_a_484_);
v___x_488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = l_Lean_MessageData_ofFormat(v___x_488_);
v___x_490_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
return v___x_491_;
}
else
{
lean_object* v___x_492_; 
lean_dec(v_a_484_);
v___x_492_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(lean_object* v_msgData_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; lean_object* v_env_500_; uint8_t v___x_501_; lean_object* v_env_502_; lean_object* v___x_503_; lean_object* v_toCold_504_; lean_object* v_mctx_505_; lean_object* v_lctx_506_; lean_object* v_options_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_499_ = lean_st_ref_get(v___y_497_);
v_env_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc_ref(v_env_500_);
lean_dec(v___x_499_);
v___x_501_ = 0;
v_env_502_ = l_Lean_Environment_setRecordingDeps(v_env_500_, v___x_501_);
v___x_503_ = lean_st_ref_get(v___y_495_);
v_toCold_504_ = lean_ctor_get(v___y_496_, 0);
v_mctx_505_ = lean_ctor_get(v___x_503_, 0);
lean_inc_ref(v_mctx_505_);
lean_dec(v___x_503_);
v_lctx_506_ = lean_ctor_get(v___y_494_, 2);
v_options_507_ = lean_ctor_get(v_toCold_504_, 2);
lean_inc_ref(v_options_507_);
lean_inc_ref(v_lctx_506_);
v___x_508_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_508_, 0, v_env_502_);
lean_ctor_set(v___x_508_, 1, v_mctx_505_);
lean_ctor_set(v___x_508_, 2, v_lctx_506_);
lean_ctor_set(v___x_508_, 3, v_options_507_);
v___x_509_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_msgData_493_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(lean_object* v_msg_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_ref_524_; lean_object* v___x_525_; lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_534_; 
v_ref_524_ = lean_ctor_get(v___y_521_, 2);
v___x_525_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msg_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_534_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
lean_inc(v_ref_524_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_ref_524_);
lean_ctor_set(v___x_530_, 1, v_a_526_);
if (v_isShared_529_ == 0)
{
lean_ctor_set_tag(v___x_528_, 1);
lean_ctor_set(v___x_528_, 0, v___x_530_);
v___x_532_ = v___x_528_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_msg_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object* v_ref_542_, lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_toCold_549_; lean_object* v_currRecDepth_550_; lean_object* v_ref_551_; uint16_t v_optionFlags_552_; uint8_t v_suppressElabErrors_553_; uint8_t v_isRecordingDeps_554_; lean_object* v_ref_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_toCold_549_ = lean_ctor_get(v___y_546_, 0);
v_currRecDepth_550_ = lean_ctor_get(v___y_546_, 1);
v_ref_551_ = lean_ctor_get(v___y_546_, 2);
v_optionFlags_552_ = lean_ctor_get_uint16(v___y_546_, sizeof(void*)*3);
v_suppressElabErrors_553_ = lean_ctor_get_uint8(v___y_546_, sizeof(void*)*3 + 2);
v_isRecordingDeps_554_ = lean_ctor_get_uint8(v___y_546_, sizeof(void*)*3 + 3);
v_ref_555_ = l_Lean_replaceRef(v_ref_542_, v_ref_551_);
lean_inc(v_currRecDepth_550_);
lean_inc_ref(v_toCold_549_);
v___x_556_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_556_, 0, v_toCold_549_);
lean_ctor_set(v___x_556_, 1, v_currRecDepth_550_);
lean_ctor_set(v___x_556_, 2, v_ref_555_);
lean_ctor_set_uint16(v___x_556_, sizeof(void*)*3, v_optionFlags_552_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*3 + 2, v_suppressElabErrors_553_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*3 + 3, v_isRecordingDeps_554_);
v___x_557_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_543_, v___y_544_, v___y_545_, v___x_556_, v___y_547_);
lean_dec_ref_known(v___x_556_, 3);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object* v_ref_558_, lean_object* v_msg_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_558_, v_msg_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v_ref_558_);
return v_res_565_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__1(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__0));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__3(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__2));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__5(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__4));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__9(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__8));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__12(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__11));
v___x_585_ = l_Lean_MessageData_ofFormat(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object* v_funName_586_, lean_object* v_extraParams_587_, lean_object* v_tb_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
uint8_t v_synthetic_594_; 
v_synthetic_594_ = lean_ctor_get_uint8(v_tb_588_, sizeof(void*)*3 + 1);
if (v_synthetic_594_ == 0)
{
lean_object* v_ref_595_; lean_object* v_vars_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v_ref_595_ = lean_ctor_get(v_tb_588_, 0);
v_vars_596_ = lean_ctor_get(v_tb_588_, 1);
v___x_597_ = lean_array_get_size(v_vars_596_);
v___x_598_ = lean_nat_dec_lt(v_extraParams_587_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v_extraParams_587_);
lean_dec(v_funName_586_);
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_msg_611_; lean_object* v___x_612_; lean_object* v_ident_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_601_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_597_);
v___x_602_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__1, &l_Lean_Elab_TerminationBy_checkVars___closed__1_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__1);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
lean_inc(v_funName_586_);
v___x_604_ = l_Lean_MessageData_ofName(v_funName_586_);
v___x_605_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__3, &l_Lean_Elab_TerminationBy_checkVars___closed__3_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__3);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_587_);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__5, &l_Lean_Elab_TerminationBy_checkVars___closed__5_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__5);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v_msg_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_611_, 0, v___x_603_);
lean_ctor_set(v_msg_611_, 1, v___x_610_);
v___x_612_ = lean_unsigned_to_nat(0u);
v_ident_613_ = lean_array_fget_borrowed(v_vars_596_, v___x_612_);
v___x_614_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__7));
lean_inc(v_ident_613_);
v___x_615_ = l_Lean_Syntax_isOfKind(v_ident_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
lean_dec(v_funName_586_);
v___x_616_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_595_, v_msg_611_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = l_Lean_TSyntax_getId(v_ident_613_);
v___x_618_ = l_Lean_Name_isSuffixOf(v___x_617_, v_funName_586_);
lean_dec(v_funName_586_);
lean_dec(v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_595_, v_msg_611_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_msg_623_; lean_object* v___x_624_; 
v___x_620_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__9, &l_Lean_Elab_TerminationBy_checkVars___closed__9_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__9);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v_msg_611_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__12, &l_Lean_Elab_TerminationBy_checkVars___closed__12_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__12);
v_msg_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_623_, 0, v___x_621_);
lean_ctor_set(v_msg_623_, 1, v___x_622_);
v___x_624_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_595_, v_msg_623_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
return v___x_624_;
}
}
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v_extraParams_587_);
lean_dec(v_funName_586_);
v___x_625_ = lean_box(0);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object* v_funName_627_, lean_object* v_extraParams_628_, lean_object* v_tb_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Elab_TerminationBy_checkVars(v_funName_627_, v_extraParams_628_, v_tb_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec_ref(v_tb_629_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_object* v_00_u03b1_636_, lean_object* v_ref_637_, lean_object* v_msg_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_637_, v_msg_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object* v_00_u03b1_645_, lean_object* v_ref_646_, lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(v_00_u03b1_645_, v_ref_646_, v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v_ref_646_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_object* v_00_u03b1_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_662_, lean_object* v_msg_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_662_, v_msg_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object* v_val_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v_val_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object* v_stx_672_, lean_object* v_terminationBy_x3f_x3f_673_, lean_object* v_terminationBy_x3f_674_, lean_object* v_partialFixpoint_x3f_675_, lean_object* v___x_676_, uint8_t v___x_677_, lean_object* v_toPure_678_, lean_object* v_decreasingBy_x3f_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_680_, 0, v_stx_672_);
lean_ctor_set(v___x_680_, 1, v_terminationBy_x3f_x3f_673_);
lean_ctor_set(v___x_680_, 2, v_terminationBy_x3f_674_);
lean_ctor_set(v___x_680_, 3, v_partialFixpoint_x3f_675_);
lean_ctor_set(v___x_680_, 4, v_decreasingBy_x3f_679_);
lean_ctor_set(v___x_680_, 5, v___x_676_);
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*6, v___x_677_);
v___x_681_ = lean_apply_2(v_toPure_678_, lean_box(0), v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed(lean_object* v_stx_682_, lean_object* v_terminationBy_x3f_x3f_683_, lean_object* v_terminationBy_x3f_684_, lean_object* v_partialFixpoint_x3f_685_, lean_object* v___x_686_, lean_object* v___x_687_, lean_object* v_toPure_688_, lean_object* v_decreasingBy_x3f_689_){
_start:
{
uint8_t v___x_2913__boxed_690_; lean_object* v_res_691_; 
v___x_2913__boxed_690_ = lean_unbox(v___x_687_);
v_res_691_ = l_Lean_Elab_elabTerminationHints___redArg___lam__1(v_stx_682_, v_terminationBy_x3f_x3f_683_, v_terminationBy_x3f_684_, v_partialFixpoint_x3f_685_, v___x_686_, v___x_2913__boxed_690_, v_toPure_688_, v_decreasingBy_x3f_689_);
return v_res_691_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1));
v___x_695_ = l_Lean_stringToMessageData(v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* v_stx_696_, lean_object* v_terminationBy_x3f_x3f_697_, lean_object* v_terminationBy_x3f_698_, lean_object* v___x_699_, uint8_t v___x_700_, lean_object* v_toPure_701_, lean_object* v_d_x3f_702_, lean_object* v_toBind_703_, lean_object* v_toFunctor_704_, lean_object* v___f_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v___x_711_, lean_object* v_partialFixpoint_x3f_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___f_714_; 
v___x_713_ = lean_box(v___x_700_);
lean_inc(v_toPure_701_);
v___f_714_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_714_, 0, v_stx_696_);
lean_closure_set(v___f_714_, 1, v_terminationBy_x3f_x3f_697_);
lean_closure_set(v___f_714_, 2, v_terminationBy_x3f_698_);
lean_closure_set(v___f_714_, 3, v_partialFixpoint_x3f_712_);
lean_closure_set(v___f_714_, 4, v___x_699_);
lean_closure_set(v___f_714_, 5, v___x_713_);
lean_closure_set(v___f_714_, 6, v_toPure_701_);
if (lean_obj_tag(v_d_x3f_702_) == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v___x_708_);
lean_dec_ref(v___x_707_);
lean_dec_ref(v___x_706_);
lean_dec_ref(v___f_705_);
lean_dec_ref(v_toFunctor_704_);
v___x_715_ = lean_box(0);
v___x_716_ = lean_apply_2(v_toPure_701_, lean_box(0), v___x_715_);
v___x_717_ = lean_apply_4(v_toBind_703_, lean_box(0), lean_box(0), v___x_716_, v___f_714_);
return v___x_717_;
}
else
{
lean_object* v_val_718_; lean_object* v_map_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_737_; 
v_val_718_ = lean_ctor_get(v_d_x3f_702_, 0);
lean_inc(v_val_718_);
lean_dec_ref_known(v_d_x3f_702_, 1);
v_map_719_ = lean_ctor_get(v_toFunctor_704_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v_toFunctor_704_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v_toFunctor_704_, 1);
lean_dec(v_unused_738_);
v___x_721_ = v_toFunctor_704_;
v_isShared_722_ = v_isSharedCheck_737_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_map_719_);
lean_dec(v_toFunctor_704_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_737_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___y_724_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_727_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0));
v___x_728_ = l_Lean_Name_mkStr4(v___x_706_, v___x_707_, v___x_708_, v___x_727_);
lean_inc(v_val_718_);
v___x_729_ = l_Lean_Syntax_isOfKind(v_val_718_, v___x_728_);
lean_dec(v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_del_object(v___x_721_);
lean_dec(v_toPure_701_);
v___x_730_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2, &l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2);
v___x_731_ = l_Lean_throwErrorAt___redArg(v_inst_709_, v_inst_710_, v_val_718_, v___x_730_);
v___y_724_ = v___x_731_;
goto v___jp_723_;
}
else
{
lean_object* v_tactic_732_; lean_object* v___x_734_; 
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
v_tactic_732_ = l_Lean_Syntax_getArg(v_val_718_, v___x_711_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v_tactic_732_);
lean_ctor_set(v___x_721_, 0, v_val_718_);
v___x_734_ = v___x_721_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_val_718_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_tactic_732_);
v___x_734_ = v_reuseFailAlloc_736_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; 
v___x_735_ = lean_apply_2(v_toPure_701_, lean_box(0), v___x_734_);
v___y_724_ = v___x_735_;
goto v___jp_723_;
}
}
v___jp_723_:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_apply_4(v_map_719_, lean_box(0), lean_box(0), v___f_705_, v___y_724_);
v___x_726_ = lean_apply_4(v_toBind_703_, lean_box(0), lean_box(0), v___x_725_, v___f_714_);
return v___x_726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_stx_739_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_740_ = _args[1];
lean_object* v_terminationBy_x3f_741_ = _args[2];
lean_object* v___x_742_ = _args[3];
lean_object* v___x_743_ = _args[4];
lean_object* v_toPure_744_ = _args[5];
lean_object* v_d_x3f_745_ = _args[6];
lean_object* v_toBind_746_ = _args[7];
lean_object* v_toFunctor_747_ = _args[8];
lean_object* v___f_748_ = _args[9];
lean_object* v___x_749_ = _args[10];
lean_object* v___x_750_ = _args[11];
lean_object* v___x_751_ = _args[12];
lean_object* v_inst_752_ = _args[13];
lean_object* v_inst_753_ = _args[14];
lean_object* v___x_754_ = _args[15];
lean_object* v_partialFixpoint_x3f_755_ = _args[16];
_start:
{
uint8_t v___x_2931__boxed_756_; lean_object* v_res_757_; 
v___x_2931__boxed_756_ = lean_unbox(v___x_743_);
v_res_757_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_739_, v_terminationBy_x3f_x3f_740_, v_terminationBy_x3f_741_, v___x_742_, v___x_2931__boxed_756_, v_toPure_744_, v_d_x3f_745_, v_toBind_746_, v_toFunctor_747_, v___f_748_, v___x_749_, v___x_750_, v___x_751_, v_inst_752_, v_inst_753_, v___x_754_, v_partialFixpoint_x3f_755_);
lean_dec(v___x_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object* v___f_758_, lean_object* v_partialFixpoint_x3f_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = lean_apply_1(v___f_758_, v_partialFixpoint_x3f_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object* v_stx_764_, lean_object* v_terminationBy_x3f_x3f_765_, lean_object* v___x_766_, uint8_t v___x_767_, lean_object* v_toPure_768_, lean_object* v_d_x3f_769_, lean_object* v_toBind_770_, lean_object* v_toFunctor_771_, lean_object* v___f_772_, lean_object* v___x_773_, lean_object* v___x_774_, lean_object* v___x_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v___x_778_, lean_object* v_t_x3f_779_, lean_object* v_terminationBy_x3f_780_){
_start:
{
lean_object* v___x_781_; lean_object* v___f_782_; 
v___x_781_ = lean_box(v___x_767_);
lean_inc(v___x_778_);
lean_inc_ref(v___x_775_);
lean_inc_ref(v___x_774_);
lean_inc_ref(v___x_773_);
lean_inc(v_toBind_770_);
lean_inc(v_toPure_768_);
v___f_782_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed), 17, 16);
lean_closure_set(v___f_782_, 0, v_stx_764_);
lean_closure_set(v___f_782_, 1, v_terminationBy_x3f_x3f_765_);
lean_closure_set(v___f_782_, 2, v_terminationBy_x3f_780_);
lean_closure_set(v___f_782_, 3, v___x_766_);
lean_closure_set(v___f_782_, 4, v___x_781_);
lean_closure_set(v___f_782_, 5, v_toPure_768_);
lean_closure_set(v___f_782_, 6, v_d_x3f_769_);
lean_closure_set(v___f_782_, 7, v_toBind_770_);
lean_closure_set(v___f_782_, 8, v_toFunctor_771_);
lean_closure_set(v___f_782_, 9, v___f_772_);
lean_closure_set(v___f_782_, 10, v___x_773_);
lean_closure_set(v___f_782_, 11, v___x_774_);
lean_closure_set(v___f_782_, 12, v___x_775_);
lean_closure_set(v___f_782_, 13, v_inst_776_);
lean_closure_set(v___f_782_, 14, v_inst_777_);
lean_closure_set(v___f_782_, 15, v___x_778_);
if (lean_obj_tag(v_t_x3f_779_) == 1)
{
lean_object* v_val_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_860_; 
v_val_783_ = lean_ctor_get(v_t_x3f_779_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_t_x3f_779_);
if (v_isSharedCheck_860_ == 0)
{
v___x_785_ = v_t_x3f_779_;
v_isShared_786_ = v_isSharedCheck_860_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_val_783_);
lean_dec(v_t_x3f_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_860_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_787_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_775_);
lean_inc_ref(v___x_774_);
lean_inc_ref(v___x_773_);
v___x_788_ = l_Lean_Name_mkStr4(v___x_773_, v___x_774_, v___x_775_, v___x_787_);
lean_inc(v_val_783_);
v___x_789_ = l_Lean_Syntax_isOfKind(v_val_783_, v___x_788_);
lean_dec(v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_790_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_775_);
lean_inc_ref(v___x_774_);
lean_inc_ref(v___x_773_);
v___x_791_ = l_Lean_Name_mkStr4(v___x_773_, v___x_774_, v___x_775_, v___x_790_);
lean_inc(v_val_783_);
v___x_792_ = l_Lean_Syntax_isOfKind(v_val_783_, v___x_791_);
lean_dec(v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_793_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_794_ = l_Lean_Name_mkStr4(v___x_773_, v___x_774_, v___x_775_, v___x_793_);
lean_inc(v_val_783_);
v___x_795_ = l_Lean_Syntax_isOfKind(v_val_783_, v___x_794_);
lean_dec(v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___f_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_del_object(v___x_785_);
lean_dec(v_val_783_);
lean_dec(v___x_778_);
v___f_796_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_796_, 0, v___f_782_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_797_);
v___x_799_ = lean_apply_4(v_toBind_770_, lean_box(0), lean_box(0), v___x_798_, v___f_796_);
return v___x_799_;
}
else
{
lean_object* v___f_800_; lean_object* v_term_x3f_802_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___f_800_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_800_, 0, v___f_782_);
v___x_810_ = l_Lean_Syntax_getArg(v_val_783_, v___x_778_);
v___x_811_ = l_Lean_Syntax_isNone(v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_810_);
v___x_813_ = l_Lean_Syntax_matchesNull(v___x_810_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec(v___x_810_);
lean_del_object(v___x_785_);
lean_dec(v_val_783_);
lean_dec(v___x_778_);
v___x_814_ = lean_box(0);
v___x_815_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_814_);
v___x_816_ = lean_apply_4(v_toBind_770_, lean_box(0), lean_box(0), v___x_815_, v___f_800_);
return v___x_816_;
}
else
{
lean_object* v_term_x3f_817_; lean_object* v___x_818_; 
v_term_x3f_817_ = l_Lean_Syntax_getArg(v___x_810_, v___x_778_);
lean_dec(v___x_778_);
lean_dec(v___x_810_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v_term_x3f_817_);
v_term_x3f_802_ = v___x_818_;
goto v___jp_801_;
}
}
else
{
lean_object* v___x_819_; 
lean_dec(v___x_810_);
lean_dec(v___x_778_);
v___x_819_ = lean_box(0);
v_term_x3f_802_ = v___x_819_;
goto v___jp_801_;
}
v___jp_801_:
{
uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_803_ = 2;
v___x_804_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_804_, 0, v_val_783_);
lean_ctor_set(v___x_804_, 1, v_term_x3f_802_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*2, v___x_803_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_804_);
v___x_806_ = v___x_785_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_809_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_806_);
v___x_808_ = lean_apply_4(v_toBind_770_, lean_box(0), lean_box(0), v___x_807_, v___f_800_);
return v___x_808_;
}
}
}
}
else
{
lean_object* v___f_820_; lean_object* v_term_x3f_822_; lean_object* v___x_830_; uint8_t v___x_831_; 
lean_dec_ref(v___x_775_);
lean_dec_ref(v___x_774_);
lean_dec_ref(v___x_773_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_820_, 0, v___f_782_);
v___x_830_ = l_Lean_Syntax_getArg(v_val_783_, v___x_778_);
v___x_831_ = l_Lean_Syntax_isNone(v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_830_);
v___x_833_ = l_Lean_Syntax_matchesNull(v___x_830_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v___x_830_);
lean_del_object(v___x_785_);
lean_dec(v_val_783_);
lean_dec(v___x_778_);
v___x_834_ = lean_box(0);
v___x_835_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_834_);
v___x_836_ = lean_apply_4(v_toBind_770_, lean_box(0), lean_box(0), v___x_835_, v___f_820_);
return v___x_836_;
}
else
{
lean_object* v_term_x3f_837_; lean_object* v___x_838_; 
v_term_x3f_837_ = l_Lean_Syntax_getArg(v___x_830_, v___x_778_);
lean_dec(v___x_778_);
lean_dec(v___x_830_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v_term_x3f_837_);
v_term_x3f_822_ = v___x_838_;
goto v___jp_821_;
}
}
else
{
lean_object* v___x_839_; 
lean_dec(v___x_830_);
lean_dec(v___x_778_);
v___x_839_ = lean_box(0);
v_term_x3f_822_ = v___x_839_;
goto v___jp_821_;
}
v___jp_821_:
{
uint8_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_823_ = 1;
v___x_824_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_824_, 0, v_val_783_);
lean_ctor_set(v___x_824_, 1, v_term_x3f_822_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*2, v___x_823_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_824_);
v___x_826_ = v___x_785_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_829_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_826_);
v___x_828_ = lean_apply_4(v_toBind_770_, lean_box(0), lean_box(0), v___x_827_, v___f_820_);
return v___x_828_;
}
}
}
}
else
{
lean_object* v___f_840_; lean_object* v_term_x3f_842_; lean_object* v___x_850_; uint8_t v___x_851_; 
lean_dec_ref(v___x_775_);
lean_dec_ref(v___x_774_);
lean_dec_ref(v___x_773_);
v___f_840_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_840_, 0, v___f_782_);
v___x_850_ = l_Lean_Syntax_getArg(v_val_783_, v___x_778_);
v___x_851_ = l_Lean_Syntax_isNone(v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_852_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_850_);
v___x_853_ = l_Lean_Syntax_matchesNull(v___x_850_, v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec(v___x_850_);
lean_del_object(v___x_785_);
lean_dec(v_val_783_);
lean_dec(v___x_778_);
v___x_854_ = lean_box(0);
v___x_855_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_854_);
v___x_856_ = lean_apply_4(v_toBind_770_, lean_box(0), lean_box(0), v___x_855_, v___f_840_);
return v___x_856_;
}
else
{
lean_object* v_term_x3f_857_; lean_object* v___x_858_; 
v_term_x3f_857_ = l_Lean_Syntax_getArg(v___x_850_, v___x_778_);
lean_dec(v___x_778_);
lean_dec(v___x_850_);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v_term_x3f_857_);
v_term_x3f_842_ = v___x_858_;
goto v___jp_841_;
}
}
else
{
lean_object* v___x_859_; 
lean_dec(v___x_850_);
lean_dec(v___x_778_);
v___x_859_ = lean_box(0);
v_term_x3f_842_ = v___x_859_;
goto v___jp_841_;
}
v___jp_841_:
{
uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_843_ = 0;
v___x_844_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_844_, 0, v_val_783_);
lean_ctor_set(v___x_844_, 1, v_term_x3f_842_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*2, v___x_843_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_844_);
v___x_846_ = v___x_785_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_849_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_846_);
v___x_848_ = lean_apply_4(v_toBind_770_, lean_box(0), lean_box(0), v___x_847_, v___f_840_);
return v___x_848_;
}
}
}
}
}
else
{
lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v_t_x3f_779_);
lean_dec(v___x_778_);
lean_dec_ref(v___x_775_);
lean_dec_ref(v___x_774_);
lean_dec_ref(v___x_773_);
v___f_861_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_861_, 0, v___f_782_);
v___x_862_ = lean_box(0);
v___x_863_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_862_);
v___x_864_ = lean_apply_4(v_toBind_770_, lean_box(0), lean_box(0), v___x_863_, v___f_861_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_stx_865_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_866_ = _args[1];
lean_object* v___x_867_ = _args[2];
lean_object* v___x_868_ = _args[3];
lean_object* v_toPure_869_ = _args[4];
lean_object* v_d_x3f_870_ = _args[5];
lean_object* v_toBind_871_ = _args[6];
lean_object* v_toFunctor_872_ = _args[7];
lean_object* v___f_873_ = _args[8];
lean_object* v___x_874_ = _args[9];
lean_object* v___x_875_ = _args[10];
lean_object* v___x_876_ = _args[11];
lean_object* v_inst_877_ = _args[12];
lean_object* v_inst_878_ = _args[13];
lean_object* v___x_879_ = _args[14];
lean_object* v_t_x3f_880_ = _args[15];
lean_object* v_terminationBy_x3f_881_ = _args[16];
_start:
{
uint8_t v___x_3020__boxed_882_; lean_object* v_res_883_; 
v___x_3020__boxed_882_ = lean_unbox(v___x_868_);
v_res_883_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11(v_stx_865_, v_terminationBy_x3f_x3f_866_, v___x_867_, v___x_3020__boxed_882_, v_toPure_869_, v_d_x3f_870_, v_toBind_871_, v_toFunctor_872_, v___f_873_, v___x_874_, v___x_875_, v___x_876_, v_inst_877_, v_inst_878_, v___x_879_, v_t_x3f_880_, v_terminationBy_x3f_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* v___f_884_, lean_object* v_terminationBy_x3f_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = lean_apply_1(v___f_884_, v_terminationBy_x3f_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4));
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* v_stx_895_, lean_object* v___x_896_, uint8_t v___x_897_, lean_object* v_toPure_898_, lean_object* v_d_x3f_899_, lean_object* v_toBind_900_, lean_object* v_toFunctor_901_, lean_object* v___f_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v___x_908_, lean_object* v_t_x3f_909_, lean_object* v_terminationBy_x3f_x3f_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___f_912_; 
v___x_911_ = lean_box(v___x_897_);
lean_inc(v_t_x3f_909_);
lean_inc(v___x_908_);
lean_inc_ref(v_inst_907_);
lean_inc_ref(v_inst_906_);
lean_inc_ref(v___x_905_);
lean_inc_ref(v___x_904_);
lean_inc_ref(v___x_903_);
lean_inc(v_toBind_900_);
lean_inc(v_toPure_898_);
lean_inc(v___x_896_);
v___f_912_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_912_, 0, v_stx_895_);
lean_closure_set(v___f_912_, 1, v_terminationBy_x3f_x3f_910_);
lean_closure_set(v___f_912_, 2, v___x_896_);
lean_closure_set(v___f_912_, 3, v___x_911_);
lean_closure_set(v___f_912_, 4, v_toPure_898_);
lean_closure_set(v___f_912_, 5, v_d_x3f_899_);
lean_closure_set(v___f_912_, 6, v_toBind_900_);
lean_closure_set(v___f_912_, 7, v_toFunctor_901_);
lean_closure_set(v___f_912_, 8, v___f_902_);
lean_closure_set(v___f_912_, 9, v___x_903_);
lean_closure_set(v___f_912_, 10, v___x_904_);
lean_closure_set(v___f_912_, 11, v___x_905_);
lean_closure_set(v___f_912_, 12, v_inst_906_);
lean_closure_set(v___f_912_, 13, v_inst_907_);
lean_closure_set(v___f_912_, 14, v___x_908_);
lean_closure_set(v___f_912_, 15, v_t_x3f_909_);
if (lean_obj_tag(v_t_x3f_909_) == 1)
{
lean_object* v_val_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_1025_; 
v_val_913_ = lean_ctor_get(v_t_x3f_909_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_t_x3f_909_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_915_ = v_t_x3f_909_;
v_isShared_916_ = v_isSharedCheck_1025_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_val_913_);
lean_dec(v_t_x3f_909_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_1025_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_917_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0));
lean_inc_ref(v___x_905_);
lean_inc_ref(v___x_904_);
lean_inc_ref(v___x_903_);
v___x_918_ = l_Lean_Name_mkStr4(v___x_903_, v___x_904_, v___x_905_, v___x_917_);
lean_inc(v_val_913_);
v___x_919_ = l_Lean_Syntax_isOfKind(v_val_913_, v___x_918_);
lean_dec(v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
lean_del_object(v___x_915_);
lean_dec(v___x_896_);
v___x_920_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1));
lean_inc_ref(v___x_905_);
lean_inc_ref(v___x_904_);
lean_inc_ref(v___x_903_);
v___x_921_ = l_Lean_Name_mkStr4(v___x_903_, v___x_904_, v___x_905_, v___x_920_);
lean_inc(v_val_913_);
v___x_922_ = l_Lean_Syntax_isOfKind(v_val_913_, v___x_921_);
lean_dec(v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_923_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_905_);
lean_inc_ref(v___x_904_);
lean_inc_ref(v___x_903_);
v___x_924_ = l_Lean_Name_mkStr4(v___x_903_, v___x_904_, v___x_905_, v___x_923_);
lean_inc(v_val_913_);
v___x_925_ = l_Lean_Syntax_isOfKind(v_val_913_, v___x_924_);
lean_dec(v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_926_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_905_);
lean_inc_ref(v___x_904_);
lean_inc_ref(v___x_903_);
v___x_927_ = l_Lean_Name_mkStr4(v___x_903_, v___x_904_, v___x_905_, v___x_926_);
lean_inc(v_val_913_);
v___x_928_ = l_Lean_Syntax_isOfKind(v_val_913_, v___x_927_);
lean_dec(v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_929_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_930_ = l_Lean_Name_mkStr4(v___x_903_, v___x_904_, v___x_905_, v___x_929_);
lean_inc(v_val_913_);
v___x_931_ = l_Lean_Syntax_isOfKind(v_val_913_, v___x_930_);
lean_dec(v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___f_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec(v___x_908_);
lean_dec(v_toPure_898_);
v___f_932_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_932_, 0, v___f_912_);
v___x_933_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_934_ = l_Lean_throwErrorAt___redArg(v_inst_906_, v_inst_907_, v_val_913_, v___x_933_);
v___x_935_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_934_, v___f_932_);
return v___x_935_;
}
else
{
lean_object* v___f_936_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___f_936_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_936_, 0, v___f_912_);
v___x_941_ = l_Lean_Syntax_getArg(v_val_913_, v___x_908_);
lean_dec(v___x_908_);
v___x_942_ = l_Lean_Syntax_isNone(v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(2u);
v___x_944_ = l_Lean_Syntax_matchesNull(v___x_941_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec(v_toPure_898_);
v___x_945_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_946_ = l_Lean_throwErrorAt___redArg(v_inst_906_, v_inst_907_, v_val_913_, v___x_945_);
v___x_947_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_946_, v___f_936_);
return v___x_947_;
}
else
{
lean_dec(v_val_913_);
lean_dec_ref(v_inst_907_);
lean_dec_ref(v_inst_906_);
goto v___jp_937_;
}
}
else
{
lean_dec(v___x_941_);
lean_dec(v_val_913_);
lean_dec_ref(v_inst_907_);
lean_dec_ref(v_inst_906_);
goto v___jp_937_;
}
v___jp_937_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_box(0);
v___x_939_ = lean_apply_2(v_toPure_898_, lean_box(0), v___x_938_);
v___x_940_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_939_, v___f_936_);
return v___x_940_;
}
}
}
else
{
lean_object* v___f_948_; lean_object* v___x_953_; uint8_t v___x_954_; 
lean_dec_ref(v___x_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
v___f_948_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_948_, 0, v___f_912_);
v___x_953_ = l_Lean_Syntax_getArg(v_val_913_, v___x_908_);
lean_dec(v___x_908_);
v___x_954_ = l_Lean_Syntax_isNone(v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = lean_unsigned_to_nat(2u);
v___x_956_ = l_Lean_Syntax_matchesNull(v___x_953_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v_toPure_898_);
v___x_957_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_958_ = l_Lean_throwErrorAt___redArg(v_inst_906_, v_inst_907_, v_val_913_, v___x_957_);
v___x_959_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_958_, v___f_948_);
return v___x_959_;
}
else
{
lean_dec(v_val_913_);
lean_dec_ref(v_inst_907_);
lean_dec_ref(v_inst_906_);
goto v___jp_949_;
}
}
else
{
lean_dec(v___x_953_);
lean_dec(v_val_913_);
lean_dec_ref(v_inst_907_);
lean_dec_ref(v_inst_906_);
goto v___jp_949_;
}
v___jp_949_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_box(0);
v___x_951_ = lean_apply_2(v_toPure_898_, lean_box(0), v___x_950_);
v___x_952_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_951_, v___f_948_);
return v___x_952_;
}
}
}
else
{
lean_object* v___f_960_; lean_object* v___x_965_; uint8_t v___x_966_; 
lean_dec_ref(v___x_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
v___f_960_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_960_, 0, v___f_912_);
v___x_965_ = l_Lean_Syntax_getArg(v_val_913_, v___x_908_);
lean_dec(v___x_908_);
v___x_966_ = l_Lean_Syntax_isNone(v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = lean_unsigned_to_nat(2u);
v___x_968_ = l_Lean_Syntax_matchesNull(v___x_965_, v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec(v_toPure_898_);
v___x_969_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_970_ = l_Lean_throwErrorAt___redArg(v_inst_906_, v_inst_907_, v_val_913_, v___x_969_);
v___x_971_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_970_, v___f_960_);
return v___x_971_;
}
else
{
lean_dec(v_val_913_);
lean_dec_ref(v_inst_907_);
lean_dec_ref(v_inst_906_);
goto v___jp_961_;
}
}
else
{
lean_dec(v___x_965_);
lean_dec(v_val_913_);
lean_dec_ref(v_inst_907_);
lean_dec_ref(v_inst_906_);
goto v___jp_961_;
}
v___jp_961_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_box(0);
v___x_963_ = lean_apply_2(v_toPure_898_, lean_box(0), v___x_962_);
v___x_964_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_963_, v___f_960_);
return v___x_964_;
}
}
}
else
{
lean_object* v___f_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec(v_val_913_);
lean_dec(v___x_908_);
lean_dec_ref(v_inst_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v___x_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
v___f_972_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_972_, 0, v___f_912_);
v___x_973_ = lean_box(0);
v___x_974_ = lean_apply_2(v_toPure_898_, lean_box(0), v___x_973_);
v___x_975_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_974_, v___f_972_);
return v___x_975_;
}
}
else
{
lean_object* v___f_976_; uint8_t v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; uint8_t v___y_981_; uint8_t v___y_989_; lean_object* v___y_990_; uint8_t v___y_991_; lean_object* v_s_998_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
lean_dec_ref(v___x_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
v___f_976_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_976_, 0, v___f_912_);
v___x_1016_ = l_Lean_Syntax_getArg(v_val_913_, v___x_908_);
v___x_1017_ = l_Lean_Syntax_isNone(v___x_1016_);
if (v___x_1017_ == 0)
{
uint8_t v___x_1018_; 
lean_inc(v___x_1016_);
v___x_1018_ = l_Lean_Syntax_matchesNull(v___x_1016_, v___x_908_);
lean_dec(v___x_908_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec(v___x_1016_);
lean_del_object(v___x_915_);
lean_dec(v_toPure_898_);
lean_dec(v___x_896_);
v___x_1019_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1020_ = l_Lean_throwErrorAt___redArg(v_inst_906_, v_inst_907_, v_val_913_, v___x_1019_);
v___x_1021_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_1020_, v___f_976_);
return v___x_1021_;
}
else
{
lean_object* v_s_1022_; lean_object* v___x_1023_; 
v_s_1022_ = l_Lean_Syntax_getArg(v___x_1016_, v___x_896_);
lean_dec(v___x_1016_);
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v_s_1022_);
v_s_998_ = v___x_1023_;
goto v___jp_997_;
}
}
else
{
lean_object* v___x_1024_; 
lean_dec(v___x_1016_);
lean_dec(v___x_908_);
v___x_1024_ = lean_box(0);
v_s_998_ = v___x_1024_;
goto v___jp_997_;
}
v___jp_977_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_982_, 0, v_val_913_);
lean_ctor_set(v___x_982_, 1, v___y_980_);
lean_ctor_set(v___x_982_, 2, v___y_979_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*3, v___y_981_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*3 + 1, v___y_978_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_982_);
v___x_984_ = v___x_915_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_987_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_apply_2(v_toPure_898_, lean_box(0), v___x_984_);
v___x_986_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_985_, v___f_976_);
return v___x_986_;
}
}
v___jp_988_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_992_ = lean_mk_empty_array_with_capacity(v___x_896_);
lean_dec(v___x_896_);
v___x_993_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_993_, 0, v_val_913_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
lean_ctor_set(v___x_993_, 2, v___y_990_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*3, v___y_991_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*3 + 1, v___y_989_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
v___x_995_ = lean_apply_2(v_toPure_898_, lean_box(0), v___x_994_);
v___x_996_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_995_, v___f_976_);
return v___x_996_;
}
v___jp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_999_ = lean_unsigned_to_nat(2u);
v___x_1000_ = l_Lean_Syntax_getArg(v_val_913_, v___x_999_);
lean_inc(v___x_1000_);
v___x_1001_ = l_Lean_Syntax_matchesNull(v___x_1000_, v___x_999_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; 
lean_del_object(v___x_915_);
v___x_1002_ = l_Lean_Syntax_matchesNull(v___x_1000_, v___x_896_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_dec(v_s_998_);
lean_dec(v_toPure_898_);
lean_dec(v___x_896_);
v___x_1003_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1004_ = l_Lean_throwErrorAt___redArg(v_inst_906_, v_inst_907_, v_val_913_, v___x_1003_);
v___x_1005_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_1004_, v___f_976_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; lean_object* v_body_1007_; 
lean_dec_ref(v_inst_907_);
lean_dec_ref(v_inst_906_);
v___x_1006_ = lean_unsigned_to_nat(3u);
v_body_1007_ = l_Lean_Syntax_getArg(v_val_913_, v___x_1006_);
if (lean_obj_tag(v_s_998_) == 0)
{
v___y_989_ = v___x_1001_;
v___y_990_ = v_body_1007_;
v___y_991_ = v___x_1001_;
goto v___jp_988_;
}
else
{
lean_dec_ref_known(v_s_998_, 1);
v___y_989_ = v___x_1001_;
v___y_990_ = v_body_1007_;
v___y_991_ = v___x_1002_;
goto v___jp_988_;
}
}
}
else
{
lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = l_Lean_Syntax_getArg(v___x_1000_, v___x_896_);
lean_dec(v___x_1000_);
lean_inc(v___x_1008_);
v___x_1009_ = l_Lean_Syntax_matchesNull(v___x_1008_, v___x_896_);
lean_dec(v___x_896_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v_body_1011_; lean_object* v_vars_1012_; 
lean_dec_ref(v_inst_907_);
lean_dec_ref(v_inst_906_);
v___x_1010_ = lean_unsigned_to_nat(3u);
v_body_1011_ = l_Lean_Syntax_getArg(v_val_913_, v___x_1010_);
v_vars_1012_ = l_Lean_Syntax_getArgs(v___x_1008_);
lean_dec(v___x_1008_);
if (lean_obj_tag(v_s_998_) == 0)
{
v___y_978_ = v___x_1009_;
v___y_979_ = v_body_1011_;
v___y_980_ = v_vars_1012_;
v___y_981_ = v___x_1009_;
goto v___jp_977_;
}
else
{
lean_dec_ref_known(v_s_998_, 1);
v___y_978_ = v___x_1009_;
v___y_979_ = v_body_1011_;
v___y_980_ = v_vars_1012_;
v___y_981_ = v___x_1001_;
goto v___jp_977_;
}
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec(v___x_1008_);
lean_dec(v_s_998_);
lean_del_object(v___x_915_);
lean_dec(v_toPure_898_);
v___x_1013_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
v___x_1014_ = l_Lean_throwErrorAt___redArg(v_inst_906_, v_inst_907_, v_val_913_, v___x_1013_);
v___x_1015_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_1014_, v___f_976_);
return v___x_1015_;
}
}
}
}
}
}
else
{
lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec(v_t_x3f_909_);
lean_dec(v___x_908_);
lean_dec_ref(v_inst_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v___x_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
lean_dec(v___x_896_);
v___f_1026_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1026_, 0, v___f_912_);
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_apply_2(v_toPure_898_, lean_box(0), v___x_1027_);
v___x_1029_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_1028_, v___f_1026_);
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed(lean_object* v_stx_1030_, lean_object* v___x_1031_, lean_object* v___x_1032_, lean_object* v_toPure_1033_, lean_object* v_d_x3f_1034_, lean_object* v_toBind_1035_, lean_object* v_toFunctor_1036_, lean_object* v___f_1037_, lean_object* v___x_1038_, lean_object* v___x_1039_, lean_object* v___x_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v___x_1043_, lean_object* v_t_x3f_1044_, lean_object* v_terminationBy_x3f_x3f_1045_){
_start:
{
uint8_t v___x_3244__boxed_1046_; lean_object* v_res_1047_; 
v___x_3244__boxed_1046_ = lean_unbox(v___x_1032_);
v_res_1047_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19(v_stx_1030_, v___x_1031_, v___x_3244__boxed_1046_, v_toPure_1033_, v_d_x3f_1034_, v_toBind_1035_, v_toFunctor_1036_, v___f_1037_, v___x_1038_, v___x_1039_, v___x_1040_, v_inst_1041_, v_inst_1042_, v___x_1043_, v_t_x3f_1044_, v_terminationBy_x3f_x3f_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* v___f_1048_, lean_object* v_terminationBy_x3f_x3f_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_apply_1(v___f_1048_, v_terminationBy_x3f_x3f_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_stx_1075_){
_start:
{
if (lean_obj_tag(v_stx_1075_) == 0)
{
lean_object* v_toApplicative_1076_; lean_object* v_toPure_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_toApplicative_1076_ = lean_ctor_get(v_inst_1073_, 0);
lean_inc_ref(v_toApplicative_1076_);
lean_dec_ref(v_inst_1074_);
lean_dec_ref(v_inst_1073_);
v_toPure_1077_ = lean_ctor_get(v_toApplicative_1076_, 1);
lean_inc(v_toPure_1077_);
lean_dec_ref(v_toApplicative_1076_);
v___x_1078_ = 1;
v___x_1079_ = lean_unsigned_to_nat(0u);
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1081_, 0, v_stx_1075_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
lean_ctor_set(v___x_1081_, 2, v___x_1080_);
lean_ctor_set(v___x_1081_, 3, v___x_1080_);
lean_ctor_set(v___x_1081_, 4, v___x_1080_);
lean_ctor_set(v___x_1081_, 5, v___x_1079_);
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*6, v___x_1078_);
v___x_1082_ = lean_apply_2(v_toPure_1077_, lean_box(0), v___x_1081_);
return v___x_1082_;
}
else
{
lean_object* v_toApplicative_1083_; lean_object* v_toBind_1084_; lean_object* v_toFunctor_1085_; lean_object* v_toPure_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_toApplicative_1083_ = lean_ctor_get(v_inst_1073_, 0);
v_toBind_1084_ = lean_ctor_get(v_inst_1073_, 1);
v_toFunctor_1085_ = lean_ctor_get(v_toApplicative_1083_, 0);
v_toPure_1086_ = lean_ctor_get(v_toApplicative_1083_, 1);
v___x_1087_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__0));
v___x_1088_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__1));
v___x_1089_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__2));
v___x_1090_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__4));
lean_inc(v_stx_1075_);
v___x_1091_ = l_Lean_Syntax_isOfKind(v_stx_1075_, v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1092_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1093_ = lean_box(0);
lean_inc_n(v_stx_1075_, 2);
v___x_1094_ = l_Lean_Syntax_formatStx(v_stx_1075_, v___x_1093_, v___x_1091_);
v___x_1095_ = l_Std_Format_defWidth;
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = l_Std_Format_pretty(v___x_1094_, v___x_1095_, v___x_1096_, v___x_1096_);
v___x_1098_ = lean_string_append(v___x_1092_, v___x_1097_);
lean_dec_ref(v___x_1097_);
v___x_1099_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1100_ = lean_string_append(v___x_1098_, v___x_1099_);
v___x_1101_ = l_Lean_Syntax_getKind(v_stx_1075_);
v___x_1102_ = 1;
v___x_1103_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1101_, v___x_1102_);
v___x_1104_ = lean_string_append(v___x_1100_, v___x_1103_);
lean_dec_ref(v___x_1103_);
v___x_1105_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
v___x_1106_ = l_Lean_MessageData_ofFormat(v___x_1105_);
v___x_1107_ = l_Lean_throwErrorAt___redArg(v_inst_1073_, v_inst_1074_, v_stx_1075_, v___x_1106_);
return v___x_1107_;
}
else
{
lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v_d_x3f_1114_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v_t_x3f_1145_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___f_1108_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__7));
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1182_ = l_Lean_Syntax_getArg(v_stx_1075_, v___x_1109_);
v___x_1183_ = l_Lean_Syntax_isNone(v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1182_);
v___x_1185_ = l_Lean_Syntax_matchesNull(v___x_1182_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec(v___x_1182_);
v___x_1186_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1187_ = lean_box(0);
lean_inc_n(v_stx_1075_, 2);
v___x_1188_ = l_Lean_Syntax_formatStx(v_stx_1075_, v___x_1187_, v___x_1185_);
v___x_1189_ = l_Std_Format_defWidth;
v___x_1190_ = l_Std_Format_pretty(v___x_1188_, v___x_1189_, v___x_1109_, v___x_1109_);
v___x_1191_ = lean_string_append(v___x_1186_, v___x_1190_);
lean_dec_ref(v___x_1190_);
v___x_1192_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1193_ = lean_string_append(v___x_1191_, v___x_1192_);
v___x_1194_ = l_Lean_Syntax_getKind(v_stx_1075_);
v___x_1195_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1194_, v___x_1091_);
v___x_1196_ = lean_string_append(v___x_1193_, v___x_1195_);
lean_dec_ref(v___x_1195_);
v___x_1197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
v___x_1198_ = l_Lean_MessageData_ofFormat(v___x_1197_);
v___x_1199_ = l_Lean_throwErrorAt___redArg(v_inst_1073_, v_inst_1074_, v_stx_1075_, v___x_1198_);
return v___x_1199_;
}
else
{
lean_object* v_t_x3f_1200_; lean_object* v___x_1201_; 
v_t_x3f_1200_ = l_Lean_Syntax_getArg(v___x_1182_, v___x_1109_);
lean_dec(v___x_1182_);
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_t_x3f_1200_);
v_t_x3f_1145_ = v___x_1201_;
goto v___jp_1144_;
}
}
else
{
lean_object* v___x_1202_; 
lean_dec(v___x_1182_);
v___x_1202_ = lean_box(0);
v_t_x3f_1145_ = v___x_1202_;
goto v___jp_1144_;
}
v___jp_1110_:
{
lean_object* v___x_1115_; lean_object* v___f_1116_; 
v___x_1115_ = lean_box(v___x_1091_);
lean_inc(v_toBind_1084_);
lean_inc(v_toPure_1086_);
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed), 16, 15);
lean_closure_set(v___f_1116_, 0, v_stx_1075_);
lean_closure_set(v___f_1116_, 1, v___x_1109_);
lean_closure_set(v___f_1116_, 2, v___x_1115_);
lean_closure_set(v___f_1116_, 3, v_toPure_1086_);
lean_closure_set(v___f_1116_, 4, v_d_x3f_1114_);
lean_closure_set(v___f_1116_, 5, v_toBind_1084_);
lean_closure_set(v___f_1116_, 6, v_toFunctor_1085_);
lean_closure_set(v___f_1116_, 7, v___f_1108_);
lean_closure_set(v___f_1116_, 8, v___x_1087_);
lean_closure_set(v___f_1116_, 9, v___x_1088_);
lean_closure_set(v___f_1116_, 10, v___x_1089_);
lean_closure_set(v___f_1116_, 11, v_inst_1073_);
lean_closure_set(v___f_1116_, 12, v_inst_1074_);
lean_closure_set(v___f_1116_, 13, v___y_1111_);
lean_closure_set(v___f_1116_, 14, v___y_1112_);
if (lean_obj_tag(v___y_1113_) == 1)
{
lean_object* v_val_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1133_; 
v_val_1117_ = lean_ctor_get(v___y_1113_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___y_1113_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1119_ = v___y_1113_;
v_isShared_1120_ = v_isSharedCheck_1133_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_val_1117_);
lean_dec(v___y_1113_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1133_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__8));
lean_inc(v_val_1117_);
v___x_1122_ = l_Lean_Syntax_isOfKind(v_val_1117_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___f_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_del_object(v___x_1119_);
lean_dec(v_val_1117_);
v___f_1123_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1123_, 0, v___f_1116_);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_apply_2(v_toPure_1086_, lean_box(0), v___x_1124_);
v___x_1126_ = lean_apply_4(v_toBind_1084_, lean_box(0), lean_box(0), v___x_1125_, v___f_1123_);
return v___x_1126_;
}
else
{
lean_object* v___f_1127_; lean_object* v___x_1129_; 
v___f_1127_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1127_, 0, v___f_1116_);
if (v_isShared_1120_ == 0)
{
v___x_1129_ = v___x_1119_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_val_1117_);
v___x_1129_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_apply_2(v_toPure_1086_, lean_box(0), v___x_1129_);
v___x_1131_ = lean_apply_4(v_toBind_1084_, lean_box(0), lean_box(0), v___x_1130_, v___f_1127_);
return v___x_1131_;
}
}
}
}
else
{
lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec(v___y_1113_);
v___f_1134_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1134_, 0, v___f_1116_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_apply_2(v_toPure_1086_, lean_box(0), v___x_1135_);
v___x_1137_ = lean_apply_4(v_toBind_1084_, lean_box(0), lean_box(0), v___x_1136_, v___f_1134_);
return v___x_1137_;
}
}
v___jp_1138_:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___y_1142_);
v___y_1111_ = v___y_1139_;
v___y_1112_ = v___y_1140_;
v___y_1113_ = v___y_1141_;
v_d_x3f_1114_ = v___x_1143_;
goto v___jp_1110_;
}
v___jp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1146_ = lean_unsigned_to_nat(1u);
v___x_1147_ = l_Lean_Syntax_getArg(v_stx_1075_, v___x_1146_);
v___x_1148_ = l_Lean_Syntax_isNone(v___x_1147_);
if (v___x_1148_ == 0)
{
uint8_t v___x_1149_; 
lean_inc(v___x_1147_);
v___x_1149_ = l_Lean_Syntax_matchesNull(v___x_1147_, v___x_1146_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec(v___x_1147_);
lean_dec(v_t_x3f_1145_);
v___x_1150_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1151_ = lean_box(0);
lean_inc_n(v_stx_1075_, 2);
v___x_1152_ = l_Lean_Syntax_formatStx(v_stx_1075_, v___x_1151_, v___x_1149_);
v___x_1153_ = l_Std_Format_defWidth;
v___x_1154_ = l_Std_Format_pretty(v___x_1152_, v___x_1153_, v___x_1109_, v___x_1109_);
v___x_1155_ = lean_string_append(v___x_1150_, v___x_1154_);
lean_dec_ref(v___x_1154_);
v___x_1156_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1157_ = lean_string_append(v___x_1155_, v___x_1156_);
v___x_1158_ = l_Lean_Syntax_getKind(v_stx_1075_);
v___x_1159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1158_, v___x_1091_);
v___x_1160_ = lean_string_append(v___x_1157_, v___x_1159_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
v___x_1162_ = l_Lean_MessageData_ofFormat(v___x_1161_);
v___x_1163_ = l_Lean_throwErrorAt___redArg(v_inst_1073_, v_inst_1074_, v_stx_1075_, v___x_1162_);
return v___x_1163_;
}
else
{
lean_object* v_d_x3f_1164_; 
v_d_x3f_1164_ = l_Lean_Syntax_getArg(v___x_1147_, v___x_1109_);
lean_dec(v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__9));
lean_inc(v_d_x3f_1164_);
v___x_1166_ = l_Lean_Syntax_isOfKind(v_d_x3f_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v_d_x3f_1164_);
lean_dec(v_t_x3f_1145_);
v___x_1167_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1168_ = lean_box(0);
lean_inc_n(v_stx_1075_, 2);
v___x_1169_ = l_Lean_Syntax_formatStx(v_stx_1075_, v___x_1168_, v___x_1148_);
v___x_1170_ = l_Std_Format_defWidth;
v___x_1171_ = l_Std_Format_pretty(v___x_1169_, v___x_1170_, v___x_1109_, v___x_1109_);
v___x_1172_ = lean_string_append(v___x_1167_, v___x_1171_);
lean_dec_ref(v___x_1171_);
v___x_1173_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1174_ = lean_string_append(v___x_1172_, v___x_1173_);
v___x_1175_ = l_Lean_Syntax_getKind(v_stx_1075_);
v___x_1176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1175_, v___x_1149_);
v___x_1177_ = lean_string_append(v___x_1174_, v___x_1176_);
lean_dec_ref(v___x_1176_);
v___x_1178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
v___x_1179_ = l_Lean_MessageData_ofFormat(v___x_1178_);
v___x_1180_ = l_Lean_throwErrorAt___redArg(v_inst_1073_, v_inst_1074_, v_stx_1075_, v___x_1179_);
return v___x_1180_;
}
else
{
lean_inc(v_toPure_1086_);
lean_inc_ref(v_toFunctor_1085_);
lean_inc(v_toBind_1084_);
lean_inc(v_t_x3f_1145_);
v___y_1139_ = v___x_1146_;
v___y_1140_ = v_t_x3f_1145_;
v___y_1141_ = v_t_x3f_1145_;
v___y_1142_ = v_d_x3f_1164_;
goto v___jp_1138_;
}
}
else
{
lean_inc(v_toPure_1086_);
lean_inc_ref(v_toFunctor_1085_);
lean_inc(v_toBind_1084_);
lean_inc(v_t_x3f_1145_);
v___y_1139_ = v___x_1146_;
v___y_1140_ = v_t_x3f_1145_;
v___y_1141_ = v_t_x3f_1145_;
v___y_1142_ = v_d_x3f_1164_;
goto v___jp_1138_;
}
}
}
else
{
lean_object* v___x_1181_; 
lean_inc(v_toPure_1086_);
lean_inc_ref(v_toFunctor_1085_);
lean_inc(v_toBind_1084_);
lean_dec(v___x_1147_);
v___x_1181_ = lean_box(0);
lean_inc(v_t_x3f_1145_);
v___y_1111_ = v___x_1146_;
v___y_1112_ = v_t_x3f_1145_;
v___y_1113_ = v_t_x3f_1145_;
v_d_x3f_1114_ = v___x_1181_;
goto v___jp_1110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* v_m_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_stx_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Elab_elabTerminationHints___redArg(v_inst_1204_, v_inst_1205_, v_stx_1206_);
return v___x_1207_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_TerminationHint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instInhabitedPartialFixpointType_default = _init_l_Lean_Elab_instInhabitedPartialFixpointType_default();
l_Lean_Elab_instInhabitedPartialFixpointType = _init_l_Lean_Elab_instInhabitedPartialFixpointType();
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_TerminationHint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_TerminationHint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_TerminationHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_TerminationHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_TerminationHint(builtin);
}
#ifdef __cplusplus
}
#endif
