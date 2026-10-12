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
lean_object* l_Lean_Elab_PartialFixpointType_ctorIdx___impl(uint8_t v_x_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_box(v_x_13_);
v___x_15_ = lean_obj_tag_nat(v___x_14_);
lean_dec(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT void l_Lean_Elab_PartialFixpointType_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_13_ = stack[0].m_num;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Elab_PartialFixpointType_ctorIdx___impl(v_x_13_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorIdx___impl___boxed(lean_object* v_x_17_){
_start:
{
uint8_t v_x_4__boxed_18_; lean_object* v_res_19_; 
v_x_4__boxed_18_ = lean_unbox(v_x_17_);
v_res_19_ = l_Lean_Elab_PartialFixpointType_ctorIdx___impl(v_x_4__boxed_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___redArg(lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___redArg___boxed(lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_PartialFixpointType_ctorElim___redArg(v_k_21_);
lean_dec(v_k_21_);
return v_res_22_;
}
}
lean_object* l_Lean_Elab_PartialFixpointType_ctorElim(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, uint8_t v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_inc(v_k_27_);
return v_k_27_;
}
}
LEAN_EXPORT void l_Lean_Elab_PartialFixpointType_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_24_ = stack[1].m_obj;
uint8_t v_t_25_ = stack[2].m_num;
lean_object* v_k_27_ = stack[4].m_obj;
lean_object* v_res_28_;
v_res_28_ = l_Lean_Elab_PartialFixpointType_ctorElim(lean_box(0), v_ctorIdx_24_, v_t_25_, lean_box(0), v_k_27_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___boxed(lean_object* v_motive_29_, lean_object* v_ctorIdx_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_k_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Elab_PartialFixpointType_ctorElim(v_motive_29_, v_ctorIdx_30_, v_t_boxed_34_, v_h_32_, v_k_33_);
lean_dec(v_k_33_);
lean_dec(v_ctorIdx_30_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(lean_object* v_partialFixpoint_36_){
_start:
{
lean_inc(v_partialFixpoint_36_);
return v_partialFixpoint_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg___boxed(lean_object* v_partialFixpoint_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(v_partialFixpoint_37_);
lean_dec(v_partialFixpoint_37_);
return v_res_38_;
}
}
lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_partialFixpoint_42_){
_start:
{
lean_inc(v_partialFixpoint_42_);
return v_partialFixpoint_42_;
}
}
LEAN_EXPORT void l_Lean_Elab_PartialFixpointType_partialFixpoint_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_40_ = stack[1].m_num;
lean_object* v_partialFixpoint_42_ = stack[3].m_obj;
lean_object* v_res_43_;
v_res_43_ = l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(lean_box(0), v_t_40_, lean_box(0), v_partialFixpoint_42_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___boxed(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_partialFixpoint_47_){
_start:
{
uint8_t v_t_boxed_48_; lean_object* v_res_49_; 
v_t_boxed_48_ = lean_unbox(v_t_45_);
v_res_49_ = l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(v_motive_44_, v_t_boxed_48_, v_h_46_, v_partialFixpoint_47_);
lean_dec(v_partialFixpoint_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(lean_object* v_coinductiveFixpoint_50_){
_start:
{
lean_inc(v_coinductiveFixpoint_50_);
return v_coinductiveFixpoint_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg___boxed(lean_object* v_coinductiveFixpoint_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(v_coinductiveFixpoint_51_);
lean_dec(v_coinductiveFixpoint_51_);
return v_res_52_;
}
}
lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(lean_object* v_motive_53_, uint8_t v_t_54_, lean_object* v_h_55_, lean_object* v_coinductiveFixpoint_56_){
_start:
{
lean_inc(v_coinductiveFixpoint_56_);
return v_coinductiveFixpoint_56_;
}
}
LEAN_EXPORT void l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_54_ = stack[1].m_num;
lean_object* v_coinductiveFixpoint_56_ = stack[3].m_obj;
lean_object* v_res_57_;
v_res_57_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(lean_box(0), v_t_54_, lean_box(0), v_coinductiveFixpoint_56_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___boxed(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_coinductiveFixpoint_61_){
_start:
{
uint8_t v_t_boxed_62_; lean_object* v_res_63_; 
v_t_boxed_62_ = lean_unbox(v_t_59_);
v_res_63_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(v_motive_58_, v_t_boxed_62_, v_h_60_, v_coinductiveFixpoint_61_);
lean_dec(v_coinductiveFixpoint_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(lean_object* v_inductiveFixpoint_64_){
_start:
{
lean_inc(v_inductiveFixpoint_64_);
return v_inductiveFixpoint_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg___boxed(lean_object* v_inductiveFixpoint_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(v_inductiveFixpoint_65_);
lean_dec(v_inductiveFixpoint_65_);
return v_res_66_;
}
}
lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(lean_object* v_motive_67_, uint8_t v_t_68_, lean_object* v_h_69_, lean_object* v_inductiveFixpoint_70_){
_start:
{
lean_inc(v_inductiveFixpoint_70_);
return v_inductiveFixpoint_70_;
}
}
LEAN_EXPORT void l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_68_ = stack[1].m_num;
lean_object* v_inductiveFixpoint_70_ = stack[3].m_obj;
lean_object* v_res_71_;
v_res_71_ = l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(lean_box(0), v_t_68_, lean_box(0), v_inductiveFixpoint_70_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___boxed(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_inductiveFixpoint_75_){
_start:
{
uint8_t v_t_boxed_76_; lean_object* v_res_77_; 
v_t_boxed_76_ = lean_unbox(v_t_73_);
v_res_77_ = l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(v_motive_72_, v_t_boxed_76_, v_h_74_, v_inductiveFixpoint_75_);
lean_dec(v_inductiveFixpoint_75_);
return v_res_77_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedPartialFixpointType_default(void){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedPartialFixpointType(void){
_start:
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
}
uint8_t l_Lean_Elab_isInductiveFixpoint(uint8_t v_x_93_){
_start:
{
if (v_x_93_ == 2)
{
uint8_t v___x_94_; 
v___x_94_ = 1;
return v___x_94_;
}
else
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_isInductiveFixpoint_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_93_ = stack[0].m_num;
uint8_t v_res_96_;
v_res_96_ = l_Lean_Elab_isInductiveFixpoint(v_x_93_);
stack->m_num = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_isInductiveFixpoint___boxed(lean_object* v_x_97_){
_start:
{
uint8_t v_x_17__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_x_17__boxed_98_ = lean_unbox(v_x_97_);
v_res_99_ = l_Lean_Elab_isInductiveFixpoint(v_x_17__boxed_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
uint8_t l_Lean_Elab_isCoinductiveFixpoint(uint8_t v_x_101_){
_start:
{
if (v_x_101_ == 1)
{
uint8_t v___x_102_; 
v___x_102_ = 1;
return v___x_102_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = 0;
return v___x_103_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_isCoinductiveFixpoint_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_101_ = stack[0].m_num;
uint8_t v_res_104_;
v_res_104_ = l_Lean_Elab_isCoinductiveFixpoint(v_x_101_);
stack->m_num = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_isCoinductiveFixpoint___boxed(lean_object* v_x_105_){
_start:
{
uint8_t v_x_17__boxed_106_; uint8_t v_res_107_; lean_object* v_r_108_; 
v_x_17__boxed_106_ = lean_unbox(v_x_105_);
v_res_107_ = l_Lean_Elab_isCoinductiveFixpoint(v_x_17__boxed_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
uint8_t l_Lean_Elab_isPartialFixpoint(uint8_t v_x_109_){
_start:
{
if (v_x_109_ == 0)
{
uint8_t v___x_110_; 
v___x_110_ = 1;
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_isPartialFixpoint_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_109_ = stack[0].m_num;
uint8_t v_res_112_;
v_res_112_ = l_Lean_Elab_isPartialFixpoint(v_x_109_);
stack->m_num = v_res_112_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_isPartialFixpoint___boxed(lean_object* v_x_113_){
_start:
{
uint8_t v_x_17__boxed_114_; uint8_t v_res_115_; lean_object* v_r_116_; 
v_x_17__boxed_114_ = lean_unbox(v_x_113_);
v_res_115_ = l_Lean_Elab_isPartialFixpoint(v_x_17__boxed_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
uint8_t l_Lean_Elab_isLatticeTheoretic(uint8_t v_p_117_){
_start:
{
uint8_t v___x_118_; 
v___x_118_ = l_Lean_Elab_isInductiveFixpoint(v_p_117_);
if (v___x_118_ == 0)
{
uint8_t v___x_119_; 
v___x_119_ = l_Lean_Elab_isCoinductiveFixpoint(v_p_117_);
return v___x_119_;
}
else
{
return v___x_118_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_isLatticeTheoretic_0interp(lean_interpreter_value* stack)
{
uint8_t v_p_117_ = stack[0].m_num;
uint8_t v_res_120_;
v_res_120_ = l_Lean_Elab_isLatticeTheoretic(v_p_117_);
stack->m_num = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_isLatticeTheoretic___boxed(lean_object* v_p_121_){
_start:
{
uint8_t v_p_boxed_122_; uint8_t v_res_123_; lean_object* v_r_124_; 
v_p_boxed_122_ = lean_unbox(v_p_121_);
v_res_123_ = l_Lean_Elab_isLatticeTheoretic(v_p_boxed_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_126_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_130_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
lean_ctor_set(v___x_132_, 2, v___x_131_);
lean_ctor_set(v___x_132_, 3, v___x_131_);
lean_ctor_set(v___x_132_, 4, v___x_130_);
lean_ctor_set(v___x_132_, 5, v___x_130_);
lean_ctor_set(v___x_132_, 6, v___x_130_);
lean_ctor_set(v___x_132_, 7, v___x_130_);
lean_ctor_set(v___x_132_, 8, v___x_130_);
lean_ctor_set(v___x_132_, 9, v___x_130_);
lean_ctor_set(v___x_132_, 10, v___x_130_);
lean_ctor_set(v___x_132_, 11, v___x_129_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_unsigned_to_nat(32u);
v___x_134_ = lean_mk_empty_array_with_capacity(v___x_133_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_136_ = ((size_t)5ULL);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_unsigned_to_nat(32u);
v___x_139_ = lean_mk_empty_array_with_capacity(v___x_138_);
v___x_140_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3);
v___x_141_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
lean_ctor_set(v___x_141_, 2, v___x_137_);
lean_ctor_set(v___x_141_, 3, v___x_137_);
lean_ctor_set_usize(v___x_141_, 4, v___x_136_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = lean_box(1);
v___x_143_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4);
v___x_144_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
v___x_145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
lean_ctor_set(v___x_145_, 2, v___x_142_);
return v___x_145_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(lean_object* v_msgData_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; lean_object* v_toCold_151_; lean_object* v_env_152_; lean_object* v_options_153_; uint8_t v___x_154_; lean_object* v_env_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_150_ = lean_st_ref_get(v___y_148_);
v_toCold_151_ = lean_ctor_get(v___y_147_, 0);
v_env_152_ = lean_ctor_get(v___x_150_, 0);
lean_inc_ref(v_env_152_);
lean_dec(v___x_150_);
v_options_153_ = lean_ctor_get(v_toCold_151_, 2);
v___x_154_ = 0;
v_env_155_ = l_Lean_Environment_setRecordingDeps(v_env_152_, v___x_154_);
v___x_156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2);
v___x_157_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_153_);
v___x_158_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_158_, 0, v_env_155_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v___x_157_);
lean_ctor_set(v___x_158_, 3, v_options_153_);
v___x_159_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v_msgData_146_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_146_ = stack[0].m_obj;
lean_object* v___y_147_ = stack[1].m_obj;
lean_object* v___y_148_ = stack[2].m_obj;
lean_object* v_res_161_;
v_res_161_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v_msgData_146_, v___y_147_, v___y_148_);
stack->m_obj
 = v_res_161_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v_msgData_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_166_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_175_, uint8_t v___y_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 1)
{
lean_object* v_pre_178_; 
v_pre_178_ = lean_ctor_get(v_x_177_, 0);
switch(lean_obj_tag(v_pre_178_))
{
case 1:
{
lean_object* v_pre_179_; 
v_pre_179_ = lean_ctor_get(v_pre_178_, 0);
switch(lean_obj_tag(v_pre_179_))
{
case 0:
{
lean_object* v_str_180_; lean_object* v_str_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_str_180_ = lean_ctor_get(v_x_177_, 1);
v_str_181_ = lean_ctor_get(v_pre_178_, 1);
v___x_182_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0));
v___x_183_ = lean_string_dec_eq(v_str_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1));
v___x_185_ = lean_string_dec_eq(v_str_181_, v___x_184_);
if (v___x_185_ == 0)
{
return v___x_185_;
}
else
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2));
v___x_187_ = lean_string_dec_eq(v_str_180_, v___x_186_);
if (v___x_187_ == 0)
{
return v___x_187_;
}
else
{
return v_suppressElabErrors_175_;
}
}
}
else
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3));
v___x_189_ = lean_string_dec_eq(v_str_180_, v___x_188_);
if (v___x_189_ == 0)
{
return v___x_189_;
}
else
{
return v_suppressElabErrors_175_;
}
}
}
case 1:
{
lean_object* v_pre_190_; 
v_pre_190_ = lean_ctor_get(v_pre_179_, 0);
if (lean_obj_tag(v_pre_190_) == 0)
{
lean_object* v_str_191_; lean_object* v_str_192_; lean_object* v_str_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_str_191_ = lean_ctor_get(v_x_177_, 1);
v_str_192_ = lean_ctor_get(v_pre_178_, 1);
v_str_193_ = lean_ctor_get(v_pre_179_, 1);
v___x_194_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4));
v___x_195_ = lean_string_dec_eq(v_str_193_, v___x_194_);
if (v___x_195_ == 0)
{
return v___x_195_;
}
else
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5));
v___x_197_ = lean_string_dec_eq(v_str_192_, v___x_196_);
if (v___x_197_ == 0)
{
return v___x_197_;
}
else
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6));
v___x_199_ = lean_string_dec_eq(v_str_191_, v___x_198_);
if (v___x_199_ == 0)
{
return v___x_199_;
}
else
{
return v_suppressElabErrors_175_;
}
}
}
}
else
{
return v___y_176_;
}
}
default: 
{
return v___y_176_;
}
}
}
case 0:
{
lean_object* v_str_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_str_200_ = lean_ctor_get(v_x_177_, 1);
v___x_201_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7));
v___x_202_ = lean_string_dec_eq(v_str_200_, v___x_201_);
if (v___x_202_ == 0)
{
return v___x_202_;
}
else
{
return v_suppressElabErrors_175_;
}
}
default: 
{
return v___y_176_;
}
}
}
else
{
return v___y_176_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_175_ = stack[0].m_num;
uint8_t v___y_176_ = stack[1].m_num;
lean_object* v_x_177_ = stack[2].m_obj;
uint8_t v_res_203_;
v_res_203_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v_suppressElabErrors_175_, v___y_176_, v_x_177_);
stack->m_num = v_res_203_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_204_, lean_object* v___y_205_, lean_object* v_x_206_){
_start:
{
uint8_t v_suppressElabErrors_boxed_207_; uint8_t v___y_3439__boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_suppressElabErrors_boxed_207_ = lean_unbox(v_suppressElabErrors_204_);
v___y_3439__boxed_208_ = lean_unbox(v___y_205_);
v_res_209_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_207_, v___y_3439__boxed_208_, v_x_206_);
lean_dec(v_x_206_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(lean_object* v_opts_211_, lean_object* v_opt_212_){
_start:
{
lean_object* v_name_213_; lean_object* v_defValue_214_; lean_object* v_map_215_; lean_object* v___x_216_; 
v_name_213_ = lean_ctor_get(v_opt_212_, 0);
v_defValue_214_ = lean_ctor_get(v_opt_212_, 1);
v_map_215_ = lean_ctor_get(v_opts_211_, 0);
v___x_216_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_215_, v_name_213_);
if (lean_obj_tag(v___x_216_) == 0)
{
uint8_t v___x_217_; 
v___x_217_ = lean_unbox(v_defValue_214_);
return v___x_217_;
}
else
{
lean_object* v_val_218_; 
v_val_218_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v___x_216_, 1);
if (lean_obj_tag(v_val_218_) == 1)
{
uint8_t v_v_219_; 
v_v_219_ = lean_ctor_get_uint8(v_val_218_, 0);
lean_dec_ref_known(v_val_218_, 0);
return v_v_219_;
}
else
{
uint8_t v___x_220_; 
lean_dec(v_val_218_);
v___x_220_ = lean_unbox(v_defValue_214_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_211_ = stack[0].m_obj;
lean_object* v_opt_212_ = stack[1].m_obj;
uint8_t v_res_221_;
v_res_221_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_opts_211_, v_opt_212_);
stack->m_num = v_res_221_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_222_, lean_object* v_opt_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_opts_222_, v_opt_223_);
lean_dec_ref(v_opt_223_);
lean_dec_ref(v_opts_222_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(lean_object* v_ref_227_, lean_object* v_msgData_228_, uint8_t v_severity_229_, uint8_t v_isSilent_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___y_235_; uint8_t v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; uint8_t v___y_240_; lean_object* v___y_241_; lean_object* v_toCold_242_; lean_object* v___y_243_; lean_object* v___y_272_; lean_object* v___y_273_; uint8_t v___y_274_; uint8_t v___y_275_; lean_object* v___y_276_; uint8_t v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; uint8_t v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; uint8_t v___y_303_; uint8_t v___y_304_; lean_object* v___y_305_; uint8_t v___y_309_; uint8_t v___y_310_; uint8_t v___y_311_; uint8_t v___x_322_; uint8_t v___y_324_; uint8_t v___y_325_; uint8_t v___y_326_; uint8_t v___y_328_; uint8_t v___x_336_; 
v___x_322_ = 2;
v___x_336_ = l_Lean_instBEqMessageSeverity_beq(v_severity_229_, v___x_322_);
if (v___x_336_ == 0)
{
v___y_328_ = v___x_336_;
goto v___jp_327_;
}
else
{
uint8_t v___x_337_; 
lean_inc_ref(v_msgData_228_);
v___x_337_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_228_);
v___y_328_ = v___x_337_;
goto v___jp_327_;
}
v___jp_234_:
{
lean_object* v_currNamespace_244_; lean_object* v_openDecls_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v_env_250_; lean_object* v_nextMacroScope_251_; lean_object* v_ngen_252_; lean_object* v_auxDeclNGen_253_; lean_object* v_traceState_254_; lean_object* v_cache_255_; lean_object* v_recordedDeps_256_; lean_object* v_messages_257_; lean_object* v_infoState_258_; lean_object* v_snapshotTasks_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_270_; 
v_currNamespace_244_ = lean_ctor_get(v_toCold_242_, 4);
v_openDecls_245_ = lean_ctor_get(v_toCold_242_, 5);
lean_inc(v_openDecls_245_);
lean_inc(v_currNamespace_244_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v_currNamespace_244_);
lean_ctor_set(v___x_246_, 1, v_openDecls_245_);
v___x_247_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___y_235_);
lean_inc_ref(v___y_238_);
lean_inc_ref(v___y_241_);
v___x_248_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_248_, 0, v___y_241_);
lean_ctor_set(v___x_248_, 1, v___y_239_);
lean_ctor_set(v___x_248_, 2, v___y_237_);
lean_ctor_set(v___x_248_, 3, v___y_238_);
lean_ctor_set(v___x_248_, 4, v___x_247_);
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*5, v___y_240_);
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*5 + 1, v___y_236_);
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*5 + 2, v_isSilent_230_);
v___x_249_ = lean_st_ref_take(v___y_243_);
v_env_250_ = lean_ctor_get(v___x_249_, 0);
v_nextMacroScope_251_ = lean_ctor_get(v___x_249_, 1);
v_ngen_252_ = lean_ctor_get(v___x_249_, 2);
v_auxDeclNGen_253_ = lean_ctor_get(v___x_249_, 3);
v_traceState_254_ = lean_ctor_get(v___x_249_, 4);
v_cache_255_ = lean_ctor_get(v___x_249_, 5);
v_recordedDeps_256_ = lean_ctor_get(v___x_249_, 6);
v_messages_257_ = lean_ctor_get(v___x_249_, 7);
v_infoState_258_ = lean_ctor_get(v___x_249_, 8);
v_snapshotTasks_259_ = lean_ctor_get(v___x_249_, 9);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_270_ == 0)
{
v___x_261_ = v___x_249_;
v_isShared_262_ = v_isSharedCheck_270_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_snapshotTasks_259_);
lean_inc(v_infoState_258_);
lean_inc(v_messages_257_);
lean_inc(v_recordedDeps_256_);
lean_inc(v_cache_255_);
lean_inc(v_traceState_254_);
lean_inc(v_auxDeclNGen_253_);
lean_inc(v_ngen_252_);
lean_inc(v_nextMacroScope_251_);
lean_inc(v_env_250_);
lean_dec(v___x_249_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_270_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_263_ = lean_box(0);
v___x_264_ = l_Lean_MessageLog_add(v___x_248_, v_messages_257_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 7, v___x_264_);
v___x_266_ = v___x_261_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_env_250_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_nextMacroScope_251_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_ngen_252_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_auxDeclNGen_253_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_traceState_254_);
lean_ctor_set(v_reuseFailAlloc_269_, 5, v_cache_255_);
lean_ctor_set(v_reuseFailAlloc_269_, 6, v_recordedDeps_256_);
lean_ctor_set(v_reuseFailAlloc_269_, 7, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_269_, 8, v_infoState_258_);
lean_ctor_set(v_reuseFailAlloc_269_, 9, v_snapshotTasks_259_);
v___x_266_ = v_reuseFailAlloc_269_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_st_ref_put(v___y_243_, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_263_);
return v___x_268_;
}
}
}
v___jp_271_:
{
lean_object* v_fileName_280_; lean_object* v_fileMap_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_297_; 
v_fileName_280_ = lean_ctor_get(v___y_278_, 0);
v_fileMap_281_ = lean_ctor_get(v___y_278_, 1);
v___x_282_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_228_);
v___x_283_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v___x_282_, v___y_231_, v___y_232_);
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_297_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_297_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_297_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_inc_ref_n(v_fileMap_281_, 2);
v___x_288_ = l_Lean_FileMap_toPosition(v_fileMap_281_, v___y_276_);
lean_dec(v___y_276_);
v___x_289_ = l_Lean_FileMap_toPosition(v_fileMap_281_, v___y_279_);
lean_dec(v___y_279_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0));
if (v___y_274_ == 0)
{
lean_del_object(v___x_286_);
lean_dec_ref(v___y_272_);
v___y_235_ = v_a_284_;
v___y_236_ = v___y_275_;
v___y_237_ = v___x_290_;
v___y_238_ = v___x_291_;
v___y_239_ = v___x_288_;
v___y_240_ = v___y_277_;
v___y_241_ = v_fileName_280_;
v_toCold_242_ = v___y_273_;
v___y_243_ = v___y_232_;
goto v___jp_234_;
}
else
{
uint8_t v___x_292_; 
lean_inc(v_a_284_);
v___x_292_ = l_Lean_MessageData_hasTag(v___y_272_, v_a_284_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_295_; 
lean_dec_ref_known(v___x_290_, 1);
lean_dec_ref(v___x_288_);
lean_dec(v_a_284_);
v___x_293_ = lean_box(0);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_293_);
v___x_295_ = v___x_286_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
else
{
lean_del_object(v___x_286_);
v___y_235_ = v_a_284_;
v___y_236_ = v___y_275_;
v___y_237_ = v___x_290_;
v___y_238_ = v___x_291_;
v___y_239_ = v___x_288_;
v___y_240_ = v___y_277_;
v___y_241_ = v_fileName_280_;
v_toCold_242_ = v___y_273_;
v___y_243_ = v___y_232_;
goto v___jp_234_;
}
}
}
}
v___jp_298_:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Syntax_getTailPos_x3f(v___y_302_, v___y_304_);
lean_dec(v___y_302_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_inc(v___y_305_);
v___y_272_ = v___y_300_;
v___y_273_ = v___y_301_;
v___y_274_ = v___y_299_;
v___y_275_ = v___y_303_;
v___y_276_ = v___y_305_;
v___y_277_ = v___y_304_;
v___y_278_ = v___y_301_;
v___y_279_ = v___y_305_;
goto v___jp_271_;
}
else
{
lean_object* v_val_307_; 
v_val_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_307_);
lean_dec_ref_known(v___x_306_, 1);
v___y_272_ = v___y_300_;
v___y_273_ = v___y_301_;
v___y_274_ = v___y_299_;
v___y_275_ = v___y_303_;
v___y_276_ = v___y_305_;
v___y_277_ = v___y_304_;
v___y_278_ = v___y_301_;
v___y_279_ = v_val_307_;
goto v___jp_271_;
}
}
v___jp_308_:
{
lean_object* v_toCold_312_; lean_object* v_ref_313_; uint8_t v_suppressElabErrors_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___f_317_; lean_object* v_ref_318_; lean_object* v___x_319_; 
v_toCold_312_ = lean_ctor_get(v___y_231_, 0);
v_ref_313_ = lean_ctor_get(v___y_231_, 2);
v_suppressElabErrors_314_ = lean_ctor_get_uint8(v___y_231_, sizeof(void*)*3 + 2);
v___x_315_ = lean_box(v_suppressElabErrors_314_);
v___x_316_ = lean_box(v___y_309_);
v___f_317_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_317_, 0, v___x_315_);
lean_closure_set(v___f_317_, 1, v___x_316_);
v_ref_318_ = l_Lean_replaceRef(v_ref_227_, v_ref_313_);
v___x_319_ = l_Lean_Syntax_getPos_x3f(v_ref_318_, v___y_310_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v___y_299_ = v_suppressElabErrors_314_;
v___y_300_ = v___f_317_;
v___y_301_ = v_toCold_312_;
v___y_302_ = v_ref_318_;
v___y_303_ = v___y_311_;
v___y_304_ = v___y_310_;
v___y_305_ = v___x_320_;
goto v___jp_298_;
}
else
{
lean_object* v_val_321_; 
v_val_321_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v___x_319_, 1);
v___y_299_ = v_suppressElabErrors_314_;
v___y_300_ = v___f_317_;
v___y_301_ = v_toCold_312_;
v___y_302_ = v_ref_318_;
v___y_303_ = v___y_311_;
v___y_304_ = v___y_310_;
v___y_305_ = v_val_321_;
goto v___jp_298_;
}
}
v___jp_323_:
{
if (v___y_326_ == 0)
{
v___y_309_ = v___y_324_;
v___y_310_ = v___y_325_;
v___y_311_ = v_severity_229_;
goto v___jp_308_;
}
else
{
v___y_309_ = v___y_324_;
v___y_310_ = v___y_325_;
v___y_311_ = v___x_322_;
goto v___jp_308_;
}
}
v___jp_327_:
{
if (v___y_328_ == 0)
{
uint8_t v___x_329_; uint8_t v___x_330_; 
v___x_329_ = 1;
v___x_330_ = l_Lean_instBEqMessageSeverity_beq(v_severity_229_, v___x_329_);
if (v___x_330_ == 0)
{
v___y_324_ = v___y_328_;
v___y_325_ = v___y_328_;
v___y_326_ = v___x_330_;
goto v___jp_323_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_331_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_231_);
v___x_332_ = l_Lean_warningAsError;
v___x_333_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v___x_331_, v___x_332_);
lean_dec_ref(v___x_331_);
v___y_324_ = v___y_328_;
v___y_325_ = v___y_328_;
v___y_326_ = v___x_333_;
goto v___jp_323_;
}
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec_ref(v_msgData_228_);
v___x_334_ = lean_box(0);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_227_ = stack[0].m_obj;
lean_object* v_msgData_228_ = stack[1].m_obj;
uint8_t v_severity_229_ = stack[2].m_num;
uint8_t v_isSilent_230_ = stack[3].m_num;
lean_object* v___y_231_ = stack[4].m_obj;
lean_object* v___y_232_ = stack[5].m_obj;
lean_object* v_res_338_;
v_res_338_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_227_, v_msgData_228_, v_severity_229_, v_isSilent_230_, v___y_231_, v___y_232_);
stack->m_obj
 = v_res_338_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___boxed(lean_object* v_ref_339_, lean_object* v_msgData_340_, lean_object* v_severity_341_, lean_object* v_isSilent_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
uint8_t v_severity_boxed_346_; uint8_t v_isSilent_boxed_347_; lean_object* v_res_348_; 
v_severity_boxed_346_ = lean_unbox(v_severity_341_);
v_isSilent_boxed_347_ = lean_unbox(v_isSilent_342_);
v_res_348_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_339_, v_msgData_340_, v_severity_boxed_346_, v_isSilent_boxed_347_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v_ref_339_);
return v_res_348_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(lean_object* v_ref_349_, lean_object* v_msgData_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
uint8_t v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; 
v___x_354_ = 1;
v___x_355_ = 0;
v___x_356_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_349_, v_msgData_350_, v___x_354_, v___x_355_, v___y_351_, v___y_352_);
return v___x_356_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_349_ = stack[0].m_obj;
lean_object* v_msgData_350_ = stack[1].m_obj;
lean_object* v___y_351_ = stack[2].m_obj;
lean_object* v___y_352_ = stack[3].m_obj;
lean_object* v_res_357_;
v_res_357_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_349_, v_msgData_350_, v___y_351_, v___y_352_);
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(lean_object* v_ref_358_, lean_object* v_msgData_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_358_, v_msgData_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v_ref_358_);
return v_res_363_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__0));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__2));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__4));
v___x_372_ = l_Lean_stringToMessageData(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__6));
v___x_375_ = l_Lean_stringToMessageData(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__8));
v___x_378_ = l_Lean_stringToMessageData(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__10));
v___x_381_ = l_Lean_stringToMessageData(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__12));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
lean_object* l_Lean_Elab_TerminationHints_ensureNone(lean_object* v_hints_385_, lean_object* v_reason_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_ref_390_; lean_object* v_terminationBy_x3f_x3f_391_; lean_object* v_terminationBy_x3f_392_; lean_object* v_partialFixpoint_x3f_393_; lean_object* v_decreasingBy_x3f_394_; uint8_t v_warnIfRedundant_395_; lean_object* v___y_397_; lean_object* v___y_398_; 
v_ref_390_ = lean_ctor_get(v_hints_385_, 0);
lean_inc(v_ref_390_);
v_terminationBy_x3f_x3f_391_ = lean_ctor_get(v_hints_385_, 1);
lean_inc(v_terminationBy_x3f_x3f_391_);
v_terminationBy_x3f_392_ = lean_ctor_get(v_hints_385_, 2);
lean_inc(v_terminationBy_x3f_392_);
v_partialFixpoint_x3f_393_ = lean_ctor_get(v_hints_385_, 3);
lean_inc(v_partialFixpoint_x3f_393_);
v_decreasingBy_x3f_394_ = lean_ctor_get(v_hints_385_, 4);
lean_inc(v_decreasingBy_x3f_394_);
v_warnIfRedundant_395_ = lean_ctor_get_uint8(v_hints_385_, sizeof(void*)*6);
lean_dec_ref(v_hints_385_);
if (v_warnIfRedundant_395_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_decreasingBy_x3f_394_);
lean_dec(v_partialFixpoint_x3f_393_);
lean_dec(v_terminationBy_x3f_392_);
lean_dec(v_terminationBy_x3f_x3f_391_);
lean_dec(v_ref_390_);
lean_dec_ref(v_reason_386_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_x3f_391_) == 0)
{
if (lean_obj_tag(v_terminationBy_x3f_392_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_394_) == 0)
{
lean_dec(v_ref_390_);
if (lean_obj_tag(v_partialFixpoint_x3f_393_) == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec_ref(v_reason_386_);
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
else
{
lean_object* v_val_407_; uint8_t v_fixpointType_408_; 
v_val_407_ = lean_ctor_get(v_partialFixpoint_x3f_393_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v_partialFixpoint_x3f_393_, 1);
v_fixpointType_408_ = lean_ctor_get_uint8(v_val_407_, sizeof(void*)*2);
switch(v_fixpointType_408_)
{
case 0:
{
lean_object* v_ref_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_ref_409_ = lean_ctor_get(v_val_407_, 0);
lean_inc(v_ref_409_);
lean_dec(v_val_407_);
v___x_410_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__3, &l_Lean_Elab_TerminationHints_ensureNone___closed__3_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3);
v___x_411_ = l_Lean_stringToMessageData(v_reason_386_);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_409_, v___x_412_, v_a_387_, v_a_388_);
lean_dec(v_ref_409_);
return v___x_413_;
}
case 1:
{
lean_object* v_ref_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_ref_414_ = lean_ctor_get(v_val_407_, 0);
lean_inc(v_ref_414_);
lean_dec(v_val_407_);
v___x_415_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__5, &l_Lean_Elab_TerminationHints_ensureNone___closed__5_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5);
v___x_416_ = l_Lean_stringToMessageData(v_reason_386_);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_414_, v___x_417_, v_a_387_, v_a_388_);
lean_dec(v_ref_414_);
return v___x_418_;
}
default: 
{
lean_object* v_ref_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_ref_419_ = lean_ctor_get(v_val_407_, 0);
lean_inc(v_ref_419_);
lean_dec(v_val_407_);
v___x_420_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__7, &l_Lean_Elab_TerminationHints_ensureNone___closed__7_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7);
v___x_421_ = l_Lean_stringToMessageData(v_reason_386_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_419_, v___x_422_, v_a_387_, v_a_388_);
lean_dec(v_ref_419_);
return v___x_423_;
}
}
}
}
else
{
if (lean_obj_tag(v_partialFixpoint_x3f_393_) == 0)
{
lean_object* v_val_424_; lean_object* v_ref_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_ref_390_);
v_val_424_ = lean_ctor_get(v_decreasingBy_x3f_394_, 0);
lean_inc(v_val_424_);
lean_dec_ref_known(v_decreasingBy_x3f_394_, 1);
v_ref_425_ = lean_ctor_get(v_val_424_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_val_424_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v_val_424_, 1);
lean_dec(v_unused_436_);
v___x_427_ = v_val_424_;
v_isShared_428_ = v_isSharedCheck_435_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_ref_425_);
lean_dec(v_val_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_435_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_429_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__9, &l_Lean_Elab_TerminationHints_ensureNone___closed__9_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9);
v___x_430_ = l_Lean_stringToMessageData(v_reason_386_);
if (v_isShared_428_ == 0)
{
lean_ctor_set_tag(v___x_427_, 7);
lean_ctor_set(v___x_427_, 1, v___x_430_);
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_432_ = v___x_427_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_430_);
v___x_432_ = v_reuseFailAlloc_434_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_425_, v___x_432_, v_a_387_, v_a_388_);
lean_dec(v_ref_425_);
return v___x_433_;
}
}
}
else
{
lean_dec_ref_known(v_decreasingBy_x3f_394_, 1);
lean_dec(v_partialFixpoint_x3f_393_);
v___y_397_ = v_a_387_;
v___y_398_ = v_a_388_;
goto v___jp_396_;
}
}
}
else
{
if (lean_obj_tag(v_decreasingBy_x3f_394_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_393_) == 0)
{
lean_object* v_val_437_; lean_object* v_ref_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v_ref_390_);
v_val_437_ = lean_ctor_get(v_terminationBy_x3f_392_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v_terminationBy_x3f_392_, 1);
v_ref_438_ = lean_ctor_get(v_val_437_, 0);
lean_inc(v_ref_438_);
lean_dec(v_val_437_);
v___x_439_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__11, &l_Lean_Elab_TerminationHints_ensureNone___closed__11_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11);
v___x_440_ = l_Lean_stringToMessageData(v_reason_386_);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_438_, v___x_441_, v_a_387_, v_a_388_);
lean_dec(v_ref_438_);
return v___x_442_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_392_, 1);
lean_dec(v_partialFixpoint_x3f_393_);
v___y_397_ = v_a_387_;
v___y_398_ = v_a_388_;
goto v___jp_396_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_392_, 1);
lean_dec(v_decreasingBy_x3f_394_);
lean_dec(v_partialFixpoint_x3f_393_);
v___y_397_ = v_a_387_;
v___y_398_ = v_a_388_;
goto v___jp_396_;
}
}
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_392_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_394_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_393_) == 0)
{
lean_object* v_val_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v_ref_390_);
v_val_443_ = lean_ctor_get(v_terminationBy_x3f_x3f_391_, 0);
lean_inc(v_val_443_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_391_, 1);
v___x_444_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__13, &l_Lean_Elab_TerminationHints_ensureNone___closed__13_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13);
v___x_445_ = l_Lean_stringToMessageData(v_reason_386_);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_val_443_, v___x_446_, v_a_387_, v_a_388_);
lean_dec(v_val_443_);
return v___x_447_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_391_, 1);
lean_dec(v_partialFixpoint_x3f_393_);
v___y_397_ = v_a_387_;
v___y_398_ = v_a_388_;
goto v___jp_396_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_391_, 1);
lean_dec(v_decreasingBy_x3f_394_);
lean_dec(v_partialFixpoint_x3f_393_);
v___y_397_ = v_a_387_;
v___y_398_ = v_a_388_;
goto v___jp_396_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_391_, 1);
lean_dec(v_decreasingBy_x3f_394_);
lean_dec(v_partialFixpoint_x3f_393_);
lean_dec(v_terminationBy_x3f_392_);
v___y_397_ = v_a_387_;
v___y_398_ = v_a_388_;
goto v___jp_396_;
}
}
}
v___jp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__1, &l_Lean_Elab_TerminationHints_ensureNone___closed__1_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1);
v___x_400_ = l_Lean_stringToMessageData(v_reason_386_);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_390_, v___x_401_, v___y_397_, v___y_398_);
lean_dec(v_ref_390_);
return v___x_402_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationHints_ensureNone_0interp(lean_interpreter_value* stack)
{
lean_object* v_hints_385_ = stack[0].m_obj;
lean_object* v_reason_386_ = stack[1].m_obj;
lean_object* v_a_387_ = stack[2].m_obj;
lean_object* v_a_388_ = stack[3].m_obj;
lean_object* v_res_448_;
v_res_448_ = l_Lean_Elab_TerminationHints_ensureNone(v_hints_385_, v_reason_386_, v_a_387_, v_a_388_);
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone___boxed(lean_object* v_hints_449_, lean_object* v_reason_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Elab_TerminationHints_ensureNone(v_hints_449_, v_reason_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
return v_res_454_;
}
}
uint8_t l_Lean_Elab_TerminationHints_isNotNone(lean_object* v_hints_455_){
_start:
{
lean_object* v_terminationBy_x3f_x3f_456_; 
v_terminationBy_x3f_x3f_456_ = lean_ctor_get(v_hints_455_, 1);
if (lean_obj_tag(v_terminationBy_x3f_x3f_456_) == 0)
{
lean_object* v_terminationBy_x3f_457_; 
v_terminationBy_x3f_457_ = lean_ctor_get(v_hints_455_, 2);
if (lean_obj_tag(v_terminationBy_x3f_457_) == 0)
{
lean_object* v_decreasingBy_x3f_458_; 
v_decreasingBy_x3f_458_ = lean_ctor_get(v_hints_455_, 4);
if (lean_obj_tag(v_decreasingBy_x3f_458_) == 0)
{
lean_object* v_partialFixpoint_x3f_459_; 
v_partialFixpoint_x3f_459_ = lean_ctor_get(v_hints_455_, 3);
if (lean_obj_tag(v_partialFixpoint_x3f_459_) == 0)
{
uint8_t v___x_460_; 
v___x_460_ = 0;
return v___x_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 1;
return v___x_461_;
}
}
else
{
uint8_t v___x_462_; 
v___x_462_ = 1;
return v___x_462_;
}
}
else
{
uint8_t v___x_463_; 
v___x_463_ = 1;
return v___x_463_;
}
}
else
{
uint8_t v___x_464_; 
v___x_464_ = 1;
return v___x_464_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationHints_isNotNone_0interp(lean_interpreter_value* stack)
{
lean_object* v_hints_455_ = stack[0].m_obj;
uint8_t v_res_465_;
v_res_465_ = l_Lean_Elab_TerminationHints_isNotNone(v_hints_455_);
stack->m_num = v_res_465_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_isNotNone___boxed(lean_object* v_hints_466_){
_start:
{
uint8_t v_res_467_; lean_object* v_r_468_; 
v_res_467_ = l_Lean_Elab_TerminationHints_isNotNone(v_hints_466_);
lean_dec_ref(v_hints_466_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object* v_headerParams_469_, lean_object* v_hints_470_, lean_object* v_value_471_){
_start:
{
lean_object* v_ref_472_; lean_object* v_terminationBy_x3f_x3f_473_; lean_object* v_terminationBy_x3f_474_; lean_object* v_partialFixpoint_x3f_475_; lean_object* v_decreasingBy_x3f_476_; uint8_t v_warnIfRedundant_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_486_; 
v_ref_472_ = lean_ctor_get(v_hints_470_, 0);
v_terminationBy_x3f_x3f_473_ = lean_ctor_get(v_hints_470_, 1);
v_terminationBy_x3f_474_ = lean_ctor_get(v_hints_470_, 2);
v_partialFixpoint_x3f_475_ = lean_ctor_get(v_hints_470_, 3);
v_decreasingBy_x3f_476_ = lean_ctor_get(v_hints_470_, 4);
v_warnIfRedundant_477_ = lean_ctor_get_uint8(v_hints_470_, sizeof(void*)*6);
v_isSharedCheck_486_ = !lean_is_exclusive(v_hints_470_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v_hints_470_, 5);
lean_dec(v_unused_487_);
v___x_479_ = v_hints_470_;
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_decreasingBy_x3f_476_);
lean_inc(v_partialFixpoint_x3f_475_);
lean_inc(v_terminationBy_x3f_474_);
lean_inc(v_terminationBy_x3f_x3f_473_);
lean_inc(v_ref_472_);
lean_dec(v_hints_470_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_481_ = l_Lean_Expr_getNumHeadLambdas(v_value_471_);
v___x_482_ = lean_nat_sub(v___x_481_, v_headerParams_469_);
lean_dec(v___x_481_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 5, v___x_482_);
v___x_484_ = v___x_479_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_ref_472_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_terminationBy_x3f_x3f_473_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_terminationBy_x3f_474_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v_partialFixpoint_x3f_475_);
lean_ctor_set(v_reuseFailAlloc_485_, 4, v_decreasingBy_x3f_476_);
lean_ctor_set(v_reuseFailAlloc_485_, 5, v___x_482_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*6, v_warnIfRedundant_477_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(lean_object* v_headerParams_488_, lean_object* v_hints_489_, lean_object* v_value_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v_headerParams_488_, v_hints_489_, v_value_490_);
lean_dec_ref(v_value_490_);
lean_dec(v_headerParams_488_);
return v_res_491_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3));
v___x_499_ = l_Lean_MessageData_ofFormat(v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(lean_object* v_a_500_){
_start:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_dec_eq(v_a_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_503_ = l_Nat_reprFast(v_a_500_);
v___x_504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
v___x_505_ = l_Lean_MessageData_ofFormat(v___x_504_);
v___x_506_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1);
v___x_507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; 
lean_dec(v_a_500_);
v___x_508_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4);
return v___x_508_;
}
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(lean_object* v_msgData_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; lean_object* v_env_516_; uint8_t v___x_517_; lean_object* v_env_518_; lean_object* v___x_519_; lean_object* v_toCold_520_; lean_object* v_mctx_521_; lean_object* v_lctx_522_; lean_object* v_options_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_515_ = lean_st_ref_get(v___y_513_);
v_env_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_ref(v_env_516_);
lean_dec(v___x_515_);
v___x_517_ = 0;
v_env_518_ = l_Lean_Environment_setRecordingDeps(v_env_516_, v___x_517_);
v___x_519_ = lean_st_ref_get(v___y_511_);
v_toCold_520_ = lean_ctor_get(v___y_512_, 0);
v_mctx_521_ = lean_ctor_get(v___x_519_, 0);
lean_inc_ref(v_mctx_521_);
lean_dec(v___x_519_);
v_lctx_522_ = lean_ctor_get(v___y_510_, 2);
v_options_523_ = lean_ctor_get(v_toCold_520_, 2);
lean_inc_ref(v_options_523_);
lean_inc_ref(v_lctx_522_);
v___x_524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_524_, 0, v_env_518_);
lean_ctor_set(v___x_524_, 1, v_mctx_521_);
lean_ctor_set(v___x_524_, 2, v_lctx_522_);
lean_ctor_set(v___x_524_, 3, v_options_523_);
v___x_525_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v_msgData_509_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_509_ = stack[0].m_obj;
lean_object* v___y_510_ = stack[1].m_obj;
lean_object* v___y_511_ = stack[2].m_obj;
lean_object* v___y_512_ = stack[3].m_obj;
lean_object* v___y_513_ = stack[4].m_obj;
lean_object* v_res_527_;
v_res_527_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_534_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(lean_object* v_msg_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_ref_541_; lean_object* v___x_542_; lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
v_ref_541_ = lean_ctor_get(v___y_538_, 2);
v___x_542_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msg_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_551_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
lean_inc(v_ref_541_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_ref_541_);
lean_ctor_set(v___x_547_, 1, v_a_543_);
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 1);
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_535_ = stack[0].m_obj;
lean_object* v___y_536_ = stack[1].m_obj;
lean_object* v___y_537_ = stack[2].m_obj;
lean_object* v___y_538_ = stack[3].m_obj;
lean_object* v___y_539_ = stack[4].m_obj;
lean_object* v_res_552_;
v_res_552_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
stack->m_obj
 = v_res_552_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_msg_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_559_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object* v_ref_560_, lean_object* v_msg_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_toCold_567_; lean_object* v_currRecDepth_568_; lean_object* v_ref_569_; uint16_t v_optionFlags_570_; uint8_t v_suppressElabErrors_571_; uint8_t v_isRecordingDeps_572_; lean_object* v_ref_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_toCold_567_ = lean_ctor_get(v___y_564_, 0);
v_currRecDepth_568_ = lean_ctor_get(v___y_564_, 1);
v_ref_569_ = lean_ctor_get(v___y_564_, 2);
v_optionFlags_570_ = lean_ctor_get_uint16(v___y_564_, sizeof(void*)*3);
v_suppressElabErrors_571_ = lean_ctor_get_uint8(v___y_564_, sizeof(void*)*3 + 2);
v_isRecordingDeps_572_ = lean_ctor_get_uint8(v___y_564_, sizeof(void*)*3 + 3);
v_ref_573_ = l_Lean_replaceRef(v_ref_560_, v_ref_569_);
lean_inc(v_currRecDepth_568_);
lean_inc_ref(v_toCold_567_);
v___x_574_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_574_, 0, v_toCold_567_);
lean_ctor_set(v___x_574_, 1, v_currRecDepth_568_);
lean_ctor_set(v___x_574_, 2, v_ref_573_);
lean_ctor_set_uint16(v___x_574_, sizeof(void*)*3, v_optionFlags_570_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*3 + 2, v_suppressElabErrors_571_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*3 + 3, v_isRecordingDeps_572_);
v___x_575_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_561_, v___y_562_, v___y_563_, v___x_574_, v___y_565_);
lean_dec_ref_known(v___x_574_, 3);
return v___x_575_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_560_ = stack[0].m_obj;
lean_object* v_msg_561_ = stack[1].m_obj;
lean_object* v___y_562_ = stack[2].m_obj;
lean_object* v___y_563_ = stack[3].m_obj;
lean_object* v___y_564_ = stack[4].m_obj;
lean_object* v___y_565_ = stack[5].m_obj;
lean_object* v_res_576_;
v_res_576_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_560_, v_msg_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object* v_ref_577_, lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_577_, v_msg_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v_ref_577_);
return v_res_584_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__1(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__0));
v___x_587_ = l_Lean_stringToMessageData(v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__3(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__2));
v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__5(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__4));
v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__9(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__8));
v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__12(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__11));
v___x_604_ = l_Lean_MessageData_ofFormat(v___x_603_);
return v___x_604_;
}
}
lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object* v_funName_605_, lean_object* v_extraParams_606_, lean_object* v_tb_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
uint8_t v_synthetic_613_; 
v_synthetic_613_ = lean_ctor_get_uint8(v_tb_607_, sizeof(void*)*3 + 1);
if (v_synthetic_613_ == 0)
{
lean_object* v_ref_614_; lean_object* v_vars_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_ref_614_ = lean_ctor_get(v_tb_607_, 0);
v_vars_615_ = lean_ctor_get(v_tb_607_, 1);
v___x_616_ = lean_array_get_size(v_vars_615_);
v___x_617_ = lean_nat_dec_lt(v_extraParams_606_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v_extraParams_606_);
lean_dec(v_funName_605_);
v___x_618_ = lean_box(0);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v_msg_630_; lean_object* v___x_631_; lean_object* v_ident_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_620_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_616_);
v___x_621_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__1, &l_Lean_Elab_TerminationBy_checkVars___closed__1_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__1);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
lean_inc(v_funName_605_);
v___x_623_ = l_Lean_MessageData_ofName(v_funName_605_);
v___x_624_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__3, &l_Lean_Elab_TerminationBy_checkVars___closed__3_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__3);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_606_);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__5, &l_Lean_Elab_TerminationBy_checkVars___closed__5_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__5);
v___x_629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v_msg_630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_630_, 0, v___x_622_);
lean_ctor_set(v_msg_630_, 1, v___x_629_);
v___x_631_ = lean_unsigned_to_nat(0u);
v_ident_632_ = lean_array_fget_borrowed(v_vars_615_, v___x_631_);
v___x_633_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__7));
lean_inc(v_ident_632_);
v___x_634_ = l_Lean_Syntax_isOfKind(v_ident_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
lean_dec(v_funName_605_);
v___x_635_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_614_, v_msg_630_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = l_Lean_TSyntax_getId(v_ident_632_);
v___x_637_ = l_Lean_Name_isSuffixOf(v___x_636_, v_funName_605_);
lean_dec(v_funName_605_);
lean_dec(v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_614_, v_msg_630_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v_msg_642_; lean_object* v___x_643_; 
v___x_639_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__9, &l_Lean_Elab_TerminationBy_checkVars___closed__9_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__9);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v_msg_630_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__12, &l_Lean_Elab_TerminationBy_checkVars___closed__12_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__12);
v_msg_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_642_, 0, v___x_640_);
lean_ctor_set(v_msg_642_, 1, v___x_641_);
v___x_643_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_614_, v_msg_642_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
return v___x_643_;
}
}
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v_extraParams_606_);
lean_dec(v_funName_605_);
v___x_644_ = lean_box(0);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationBy_checkVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_funName_605_ = stack[0].m_obj;
lean_object* v_extraParams_606_ = stack[1].m_obj;
lean_object* v_tb_607_ = stack[2].m_obj;
lean_object* v_a_608_ = stack[3].m_obj;
lean_object* v_a_609_ = stack[4].m_obj;
lean_object* v_a_610_ = stack[5].m_obj;
lean_object* v_a_611_ = stack[6].m_obj;
lean_object* v_res_646_;
v_res_646_ = l_Lean_Elab_TerminationBy_checkVars(v_funName_605_, v_extraParams_606_, v_tb_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
stack->m_obj
 = v_res_646_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object* v_funName_647_, lean_object* v_extraParams_648_, lean_object* v_tb_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Elab_TerminationBy_checkVars(v_funName_647_, v_extraParams_648_, v_tb_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec_ref(v_tb_649_);
return v_res_655_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_object* v_00_u03b1_656_, lean_object* v_ref_657_, lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_657_, v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
return v___x_664_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_657_ = stack[1].m_obj;
lean_object* v_msg_658_ = stack[2].m_obj;
lean_object* v___y_659_ = stack[3].m_obj;
lean_object* v___y_660_ = stack[4].m_obj;
lean_object* v___y_661_ = stack[5].m_obj;
lean_object* v___y_662_ = stack[6].m_obj;
lean_object* v_res_665_;
v_res_665_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_box(0), v_ref_657_, v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
stack->m_obj
 = v_res_665_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object* v_00_u03b1_666_, lean_object* v_ref_667_, lean_object* v_msg_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(v_00_u03b1_666_, v_ref_667_, v_msg_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v_ref_667_);
return v_res_674_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_object* v_00_u03b1_675_, lean_object* v_msg_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
return v___x_682_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_676_ = stack[1].m_obj;
lean_object* v___y_677_ = stack[2].m_obj;
lean_object* v___y_678_ = stack[3].m_obj;
lean_object* v___y_679_ = stack[4].m_obj;
lean_object* v___y_680_ = stack[5].m_obj;
lean_object* v_res_683_;
v_res_683_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_box(0), v_msg_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
stack->m_obj
 = v_res_683_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_684_, lean_object* v_msg_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_684_, v_msg_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object* v_val_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v_val_692_);
return v___x_693_;
}
}
lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object* v_stx_694_, lean_object* v_terminationBy_x3f_x3f_695_, lean_object* v_terminationBy_x3f_696_, lean_object* v_partialFixpoint_x3f_697_, lean_object* v___x_698_, uint8_t v___x_699_, lean_object* v_toPure_700_, lean_object* v_decreasingBy_x3f_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_702_, 0, v_stx_694_);
lean_ctor_set(v___x_702_, 1, v_terminationBy_x3f_x3f_695_);
lean_ctor_set(v___x_702_, 2, v_terminationBy_x3f_696_);
lean_ctor_set(v___x_702_, 3, v_partialFixpoint_x3f_697_);
lean_ctor_set(v___x_702_, 4, v_decreasingBy_x3f_701_);
lean_ctor_set(v___x_702_, 5, v___x_698_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*6, v___x_699_);
v___x_703_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT void l_Lean_Elab_elabTerminationHints___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_694_ = stack[0].m_obj;
lean_object* v_terminationBy_x3f_x3f_695_ = stack[1].m_obj;
lean_object* v_terminationBy_x3f_696_ = stack[2].m_obj;
lean_object* v_partialFixpoint_x3f_697_ = stack[3].m_obj;
lean_object* v___x_698_ = stack[4].m_obj;
uint8_t v___x_699_ = stack[5].m_num;
lean_object* v_toPure_700_ = stack[6].m_obj;
lean_object* v_decreasingBy_x3f_701_ = stack[7].m_obj;
lean_object* v_res_704_;
v_res_704_ = l_Lean_Elab_elabTerminationHints___redArg___lam__1(v_stx_694_, v_terminationBy_x3f_x3f_695_, v_terminationBy_x3f_696_, v_partialFixpoint_x3f_697_, v___x_698_, v___x_699_, v_toPure_700_, v_decreasingBy_x3f_701_);
stack->m_obj
 = v_res_704_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed(lean_object* v_stx_705_, lean_object* v_terminationBy_x3f_x3f_706_, lean_object* v_terminationBy_x3f_707_, lean_object* v_partialFixpoint_x3f_708_, lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v_toPure_711_, lean_object* v_decreasingBy_x3f_712_){
_start:
{
uint8_t v___x_2914__boxed_713_; lean_object* v_res_714_; 
v___x_2914__boxed_713_ = lean_unbox(v___x_710_);
v_res_714_ = l_Lean_Elab_elabTerminationHints___redArg___lam__1(v_stx_705_, v_terminationBy_x3f_x3f_706_, v_terminationBy_x3f_707_, v_partialFixpoint_x3f_708_, v___x_709_, v___x_2914__boxed_713_, v_toPure_711_, v_decreasingBy_x3f_712_);
return v_res_714_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1));
v___x_718_ = l_Lean_stringToMessageData(v___x_717_);
return v___x_718_;
}
}
lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* v_stx_719_, lean_object* v_terminationBy_x3f_x3f_720_, lean_object* v_terminationBy_x3f_721_, lean_object* v___x_722_, uint8_t v___x_723_, lean_object* v_toPure_724_, lean_object* v_d_x3f_725_, lean_object* v_toBind_726_, lean_object* v_toFunctor_727_, lean_object* v___f_728_, lean_object* v___x_729_, lean_object* v___x_730_, lean_object* v___x_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v___x_734_, lean_object* v_partialFixpoint_x3f_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___f_737_; 
v___x_736_ = lean_box(v___x_723_);
lean_inc(v_toPure_724_);
v___f_737_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_737_, 0, v_stx_719_);
lean_closure_set(v___f_737_, 1, v_terminationBy_x3f_x3f_720_);
lean_closure_set(v___f_737_, 2, v_terminationBy_x3f_721_);
lean_closure_set(v___f_737_, 3, v_partialFixpoint_x3f_735_);
lean_closure_set(v___f_737_, 4, v___x_722_);
lean_closure_set(v___f_737_, 5, v___x_736_);
lean_closure_set(v___f_737_, 6, v_toPure_724_);
if (lean_obj_tag(v_d_x3f_725_) == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec_ref(v_inst_733_);
lean_dec_ref(v_inst_732_);
lean_dec_ref(v___x_731_);
lean_dec_ref(v___x_730_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___f_728_);
lean_dec_ref(v_toFunctor_727_);
v___x_738_ = lean_box(0);
v___x_739_ = lean_apply_2(v_toPure_724_, lean_box(0), v___x_738_);
v___x_740_ = lean_apply_4(v_toBind_726_, lean_box(0), lean_box(0), v___x_739_, v___f_737_);
return v___x_740_;
}
else
{
lean_object* v_val_741_; lean_object* v_map_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_760_; 
v_val_741_ = lean_ctor_get(v_d_x3f_725_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v_d_x3f_725_, 1);
v_map_742_ = lean_ctor_get(v_toFunctor_727_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_toFunctor_727_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v_toFunctor_727_, 1);
lean_dec(v_unused_761_);
v___x_744_ = v_toFunctor_727_;
v_isShared_745_ = v_isSharedCheck_760_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_map_742_);
lean_dec(v_toFunctor_727_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_760_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___y_747_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0));
v___x_751_ = l_Lean_Name_mkStr4(v___x_729_, v___x_730_, v___x_731_, v___x_750_);
lean_inc(v_val_741_);
v___x_752_ = l_Lean_Syntax_isOfKind(v_val_741_, v___x_751_);
lean_dec(v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_del_object(v___x_744_);
lean_dec(v_toPure_724_);
v___x_753_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2, &l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2);
v___x_754_ = l_Lean_throwErrorAt___redArg(v_inst_732_, v_inst_733_, v_val_741_, v___x_753_);
v___y_747_ = v___x_754_;
goto v___jp_746_;
}
else
{
lean_object* v_tactic_755_; lean_object* v___x_757_; 
lean_dec_ref(v_inst_733_);
lean_dec_ref(v_inst_732_);
v_tactic_755_ = l_Lean_Syntax_getArg(v_val_741_, v___x_734_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v_tactic_755_);
lean_ctor_set(v___x_744_, 0, v_val_741_);
v___x_757_ = v___x_744_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_val_741_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_tactic_755_);
v___x_757_ = v_reuseFailAlloc_759_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; 
v___x_758_ = lean_apply_2(v_toPure_724_, lean_box(0), v___x_757_);
v___y_747_ = v___x_758_;
goto v___jp_746_;
}
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_apply_4(v_map_742_, lean_box(0), lean_box(0), v___f_728_, v___y_747_);
v___x_749_ = lean_apply_4(v_toBind_726_, lean_box(0), lean_box(0), v___x_748_, v___f_737_);
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_elabTerminationHints___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_719_ = stack[0].m_obj;
lean_object* v_terminationBy_x3f_x3f_720_ = stack[1].m_obj;
lean_object* v_terminationBy_x3f_721_ = stack[2].m_obj;
lean_object* v___x_722_ = stack[3].m_obj;
uint8_t v___x_723_ = stack[4].m_num;
lean_object* v_toPure_724_ = stack[5].m_obj;
lean_object* v_d_x3f_725_ = stack[6].m_obj;
lean_object* v_toBind_726_ = stack[7].m_obj;
lean_object* v_toFunctor_727_ = stack[8].m_obj;
lean_object* v___f_728_ = stack[9].m_obj;
lean_object* v___x_729_ = stack[10].m_obj;
lean_object* v___x_730_ = stack[11].m_obj;
lean_object* v___x_731_ = stack[12].m_obj;
lean_object* v_inst_732_ = stack[13].m_obj;
lean_object* v_inst_733_ = stack[14].m_obj;
lean_object* v___x_734_ = stack[15].m_obj;
lean_object* v_partialFixpoint_x3f_735_ = stack[16].m_obj;
lean_object* v_res_762_;
v_res_762_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_719_, v_terminationBy_x3f_x3f_720_, v_terminationBy_x3f_721_, v___x_722_, v___x_723_, v_toPure_724_, v_d_x3f_725_, v_toBind_726_, v_toFunctor_727_, v___f_728_, v___x_729_, v___x_730_, v___x_731_, v_inst_732_, v_inst_733_, v___x_734_, v_partialFixpoint_x3f_735_);
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_stx_763_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_764_ = _args[1];
lean_object* v_terminationBy_x3f_765_ = _args[2];
lean_object* v___x_766_ = _args[3];
lean_object* v___x_767_ = _args[4];
lean_object* v_toPure_768_ = _args[5];
lean_object* v_d_x3f_769_ = _args[6];
lean_object* v_toBind_770_ = _args[7];
lean_object* v_toFunctor_771_ = _args[8];
lean_object* v___f_772_ = _args[9];
lean_object* v___x_773_ = _args[10];
lean_object* v___x_774_ = _args[11];
lean_object* v___x_775_ = _args[12];
lean_object* v_inst_776_ = _args[13];
lean_object* v_inst_777_ = _args[14];
lean_object* v___x_778_ = _args[15];
lean_object* v_partialFixpoint_x3f_779_ = _args[16];
_start:
{
uint8_t v___x_2938__boxed_780_; lean_object* v_res_781_; 
v___x_2938__boxed_780_ = lean_unbox(v___x_767_);
v_res_781_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_763_, v_terminationBy_x3f_x3f_764_, v_terminationBy_x3f_765_, v___x_766_, v___x_2938__boxed_780_, v_toPure_768_, v_d_x3f_769_, v_toBind_770_, v_toFunctor_771_, v___f_772_, v___x_773_, v___x_774_, v___x_775_, v_inst_776_, v_inst_777_, v___x_778_, v_partialFixpoint_x3f_779_);
lean_dec(v___x_778_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object* v___f_782_, lean_object* v_partialFixpoint_x3f_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = lean_apply_1(v___f_782_, v_partialFixpoint_x3f_783_);
return v___x_784_;
}
}
lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object* v_stx_788_, lean_object* v_terminationBy_x3f_x3f_789_, lean_object* v___x_790_, uint8_t v___x_791_, lean_object* v_toPure_792_, lean_object* v_d_x3f_793_, lean_object* v_toBind_794_, lean_object* v_toFunctor_795_, lean_object* v___f_796_, lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v___x_799_, lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v___x_802_, lean_object* v_t_x3f_803_, lean_object* v_terminationBy_x3f_804_){
_start:
{
lean_object* v___x_805_; lean_object* v___f_806_; 
v___x_805_ = lean_box(v___x_791_);
lean_inc(v___x_802_);
lean_inc_ref(v___x_799_);
lean_inc_ref(v___x_798_);
lean_inc_ref(v___x_797_);
lean_inc(v_toBind_794_);
lean_inc(v_toPure_792_);
v___f_806_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed), 17, 16);
lean_closure_set(v___f_806_, 0, v_stx_788_);
lean_closure_set(v___f_806_, 1, v_terminationBy_x3f_x3f_789_);
lean_closure_set(v___f_806_, 2, v_terminationBy_x3f_804_);
lean_closure_set(v___f_806_, 3, v___x_790_);
lean_closure_set(v___f_806_, 4, v___x_805_);
lean_closure_set(v___f_806_, 5, v_toPure_792_);
lean_closure_set(v___f_806_, 6, v_d_x3f_793_);
lean_closure_set(v___f_806_, 7, v_toBind_794_);
lean_closure_set(v___f_806_, 8, v_toFunctor_795_);
lean_closure_set(v___f_806_, 9, v___f_796_);
lean_closure_set(v___f_806_, 10, v___x_797_);
lean_closure_set(v___f_806_, 11, v___x_798_);
lean_closure_set(v___f_806_, 12, v___x_799_);
lean_closure_set(v___f_806_, 13, v_inst_800_);
lean_closure_set(v___f_806_, 14, v_inst_801_);
lean_closure_set(v___f_806_, 15, v___x_802_);
if (lean_obj_tag(v_t_x3f_803_) == 1)
{
lean_object* v_val_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_884_; 
v_val_807_ = lean_ctor_get(v_t_x3f_803_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_t_x3f_803_);
if (v_isSharedCheck_884_ == 0)
{
v___x_809_ = v_t_x3f_803_;
v_isShared_810_ = v_isSharedCheck_884_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_val_807_);
lean_dec(v_t_x3f_803_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_884_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_811_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_799_);
lean_inc_ref(v___x_798_);
lean_inc_ref(v___x_797_);
v___x_812_ = l_Lean_Name_mkStr4(v___x_797_, v___x_798_, v___x_799_, v___x_811_);
lean_inc(v_val_807_);
v___x_813_ = l_Lean_Syntax_isOfKind(v_val_807_, v___x_812_);
lean_dec(v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_814_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_799_);
lean_inc_ref(v___x_798_);
lean_inc_ref(v___x_797_);
v___x_815_ = l_Lean_Name_mkStr4(v___x_797_, v___x_798_, v___x_799_, v___x_814_);
lean_inc(v_val_807_);
v___x_816_ = l_Lean_Syntax_isOfKind(v_val_807_, v___x_815_);
lean_dec(v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_817_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_818_ = l_Lean_Name_mkStr4(v___x_797_, v___x_798_, v___x_799_, v___x_817_);
lean_inc(v_val_807_);
v___x_819_ = l_Lean_Syntax_isOfKind(v_val_807_, v___x_818_);
lean_dec(v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_del_object(v___x_809_);
lean_dec(v_val_807_);
lean_dec(v___x_802_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_820_, 0, v___f_806_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_821_);
v___x_823_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_822_, v___f_820_);
return v___x_823_;
}
else
{
lean_object* v___f_824_; lean_object* v_term_x3f_826_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___f_824_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_824_, 0, v___f_806_);
v___x_834_ = l_Lean_Syntax_getArg(v_val_807_, v___x_802_);
v___x_835_ = l_Lean_Syntax_isNone(v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_834_);
v___x_837_ = l_Lean_Syntax_matchesNull(v___x_834_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v___x_834_);
lean_del_object(v___x_809_);
lean_dec(v_val_807_);
lean_dec(v___x_802_);
v___x_838_ = lean_box(0);
v___x_839_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_838_);
v___x_840_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_839_, v___f_824_);
return v___x_840_;
}
else
{
lean_object* v_term_x3f_841_; lean_object* v___x_842_; 
v_term_x3f_841_ = l_Lean_Syntax_getArg(v___x_834_, v___x_802_);
lean_dec(v___x_802_);
lean_dec(v___x_834_);
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v_term_x3f_841_);
v_term_x3f_826_ = v___x_842_;
goto v___jp_825_;
}
}
else
{
lean_object* v___x_843_; 
lean_dec(v___x_834_);
lean_dec(v___x_802_);
v___x_843_ = lean_box(0);
v_term_x3f_826_ = v___x_843_;
goto v___jp_825_;
}
v___jp_825_:
{
uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = 2;
v___x_828_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_828_, 0, v_val_807_);
lean_ctor_set(v___x_828_, 1, v_term_x3f_826_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*2, v___x_827_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_828_);
v___x_830_ = v___x_809_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_833_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_830_);
v___x_832_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_831_, v___f_824_);
return v___x_832_;
}
}
}
}
else
{
lean_object* v___f_844_; lean_object* v_term_x3f_846_; lean_object* v___x_854_; uint8_t v___x_855_; 
lean_dec_ref(v___x_799_);
lean_dec_ref(v___x_798_);
lean_dec_ref(v___x_797_);
v___f_844_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_844_, 0, v___f_806_);
v___x_854_ = l_Lean_Syntax_getArg(v_val_807_, v___x_802_);
v___x_855_ = l_Lean_Syntax_isNone(v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_854_);
v___x_857_ = l_Lean_Syntax_matchesNull(v___x_854_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec(v___x_854_);
lean_del_object(v___x_809_);
lean_dec(v_val_807_);
lean_dec(v___x_802_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_858_);
v___x_860_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_859_, v___f_844_);
return v___x_860_;
}
else
{
lean_object* v_term_x3f_861_; lean_object* v___x_862_; 
v_term_x3f_861_ = l_Lean_Syntax_getArg(v___x_854_, v___x_802_);
lean_dec(v___x_802_);
lean_dec(v___x_854_);
v___x_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_862_, 0, v_term_x3f_861_);
v_term_x3f_846_ = v___x_862_;
goto v___jp_845_;
}
}
else
{
lean_object* v___x_863_; 
lean_dec(v___x_854_);
lean_dec(v___x_802_);
v___x_863_ = lean_box(0);
v_term_x3f_846_ = v___x_863_;
goto v___jp_845_;
}
v___jp_845_:
{
uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_847_ = 1;
v___x_848_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_848_, 0, v_val_807_);
lean_ctor_set(v___x_848_, 1, v_term_x3f_846_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*2, v___x_847_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_848_);
v___x_850_ = v___x_809_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_853_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_850_);
v___x_852_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_851_, v___f_844_);
return v___x_852_;
}
}
}
}
else
{
lean_object* v___f_864_; lean_object* v_term_x3f_866_; lean_object* v___x_874_; uint8_t v___x_875_; 
lean_dec_ref(v___x_799_);
lean_dec_ref(v___x_798_);
lean_dec_ref(v___x_797_);
v___f_864_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_864_, 0, v___f_806_);
v___x_874_ = l_Lean_Syntax_getArg(v_val_807_, v___x_802_);
v___x_875_ = l_Lean_Syntax_isNone(v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_874_);
v___x_877_ = l_Lean_Syntax_matchesNull(v___x_874_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec(v___x_874_);
lean_del_object(v___x_809_);
lean_dec(v_val_807_);
lean_dec(v___x_802_);
v___x_878_ = lean_box(0);
v___x_879_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_878_);
v___x_880_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_879_, v___f_864_);
return v___x_880_;
}
else
{
lean_object* v_term_x3f_881_; lean_object* v___x_882_; 
v_term_x3f_881_ = l_Lean_Syntax_getArg(v___x_874_, v___x_802_);
lean_dec(v___x_802_);
lean_dec(v___x_874_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v_term_x3f_881_);
v_term_x3f_866_ = v___x_882_;
goto v___jp_865_;
}
}
else
{
lean_object* v___x_883_; 
lean_dec(v___x_874_);
lean_dec(v___x_802_);
v___x_883_ = lean_box(0);
v_term_x3f_866_ = v___x_883_;
goto v___jp_865_;
}
v___jp_865_:
{
uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_867_ = 0;
v___x_868_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_868_, 0, v_val_807_);
lean_ctor_set(v___x_868_, 1, v_term_x3f_866_);
lean_ctor_set_uint8(v___x_868_, sizeof(void*)*2, v___x_867_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_868_);
v___x_870_ = v___x_809_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_873_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_870_);
v___x_872_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_871_, v___f_864_);
return v___x_872_;
}
}
}
}
}
else
{
lean_object* v___f_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec(v_t_x3f_803_);
lean_dec(v___x_802_);
lean_dec_ref(v___x_799_);
lean_dec_ref(v___x_798_);
lean_dec_ref(v___x_797_);
v___f_885_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_885_, 0, v___f_806_);
v___x_886_ = lean_box(0);
v___x_887_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_886_);
v___x_888_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_887_, v___f_885_);
return v___x_888_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_elabTerminationHints___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_788_ = stack[0].m_obj;
lean_object* v_terminationBy_x3f_x3f_789_ = stack[1].m_obj;
lean_object* v___x_790_ = stack[2].m_obj;
uint8_t v___x_791_ = stack[3].m_num;
lean_object* v_toPure_792_ = stack[4].m_obj;
lean_object* v_d_x3f_793_ = stack[5].m_obj;
lean_object* v_toBind_794_ = stack[6].m_obj;
lean_object* v_toFunctor_795_ = stack[7].m_obj;
lean_object* v___f_796_ = stack[8].m_obj;
lean_object* v___x_797_ = stack[9].m_obj;
lean_object* v___x_798_ = stack[10].m_obj;
lean_object* v___x_799_ = stack[11].m_obj;
lean_object* v_inst_800_ = stack[12].m_obj;
lean_object* v_inst_801_ = stack[13].m_obj;
lean_object* v___x_802_ = stack[14].m_obj;
lean_object* v_t_x3f_803_ = stack[15].m_obj;
lean_object* v_terminationBy_x3f_804_ = stack[16].m_obj;
lean_object* v_res_889_;
v_res_889_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11(v_stx_788_, v_terminationBy_x3f_x3f_789_, v___x_790_, v___x_791_, v_toPure_792_, v_d_x3f_793_, v_toBind_794_, v_toFunctor_795_, v___f_796_, v___x_797_, v___x_798_, v___x_799_, v_inst_800_, v_inst_801_, v___x_802_, v_t_x3f_803_, v_terminationBy_x3f_804_);
stack->m_obj
 = v_res_889_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_stx_890_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_891_ = _args[1];
lean_object* v___x_892_ = _args[2];
lean_object* v___x_893_ = _args[3];
lean_object* v_toPure_894_ = _args[4];
lean_object* v_d_x3f_895_ = _args[5];
lean_object* v_toBind_896_ = _args[6];
lean_object* v_toFunctor_897_ = _args[7];
lean_object* v___f_898_ = _args[8];
lean_object* v___x_899_ = _args[9];
lean_object* v___x_900_ = _args[10];
lean_object* v___x_901_ = _args[11];
lean_object* v_inst_902_ = _args[12];
lean_object* v_inst_903_ = _args[13];
lean_object* v___x_904_ = _args[14];
lean_object* v_t_x3f_905_ = _args[15];
lean_object* v_terminationBy_x3f_906_ = _args[16];
_start:
{
uint8_t v___x_3075__boxed_907_; lean_object* v_res_908_; 
v___x_3075__boxed_907_ = lean_unbox(v___x_893_);
v_res_908_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11(v_stx_890_, v_terminationBy_x3f_x3f_891_, v___x_892_, v___x_3075__boxed_907_, v_toPure_894_, v_d_x3f_895_, v_toBind_896_, v_toFunctor_897_, v___f_898_, v___x_899_, v___x_900_, v___x_901_, v_inst_902_, v_inst_903_, v___x_904_, v_t_x3f_905_, v_terminationBy_x3f_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* v___f_909_, lean_object* v_terminationBy_x3f_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = lean_apply_1(v___f_909_, v_terminationBy_x3f_910_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2));
v___x_916_ = l_Lean_stringToMessageData(v___x_915_);
return v___x_916_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4));
v___x_919_ = l_Lean_stringToMessageData(v___x_918_);
return v___x_919_;
}
}
lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* v_stx_920_, lean_object* v___x_921_, uint8_t v___x_922_, lean_object* v_toPure_923_, lean_object* v_d_x3f_924_, lean_object* v_toBind_925_, lean_object* v_toFunctor_926_, lean_object* v___f_927_, lean_object* v___x_928_, lean_object* v___x_929_, lean_object* v___x_930_, lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v___x_933_, lean_object* v_t_x3f_934_, lean_object* v_terminationBy_x3f_x3f_935_){
_start:
{
lean_object* v___x_936_; lean_object* v___f_937_; 
v___x_936_ = lean_box(v___x_922_);
lean_inc(v_t_x3f_934_);
lean_inc(v___x_933_);
lean_inc_ref(v_inst_932_);
lean_inc_ref(v_inst_931_);
lean_inc_ref(v___x_930_);
lean_inc_ref(v___x_929_);
lean_inc_ref(v___x_928_);
lean_inc(v_toBind_925_);
lean_inc(v_toPure_923_);
lean_inc(v___x_921_);
v___f_937_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_937_, 0, v_stx_920_);
lean_closure_set(v___f_937_, 1, v_terminationBy_x3f_x3f_935_);
lean_closure_set(v___f_937_, 2, v___x_921_);
lean_closure_set(v___f_937_, 3, v___x_936_);
lean_closure_set(v___f_937_, 4, v_toPure_923_);
lean_closure_set(v___f_937_, 5, v_d_x3f_924_);
lean_closure_set(v___f_937_, 6, v_toBind_925_);
lean_closure_set(v___f_937_, 7, v_toFunctor_926_);
lean_closure_set(v___f_937_, 8, v___f_927_);
lean_closure_set(v___f_937_, 9, v___x_928_);
lean_closure_set(v___f_937_, 10, v___x_929_);
lean_closure_set(v___f_937_, 11, v___x_930_);
lean_closure_set(v___f_937_, 12, v_inst_931_);
lean_closure_set(v___f_937_, 13, v_inst_932_);
lean_closure_set(v___f_937_, 14, v___x_933_);
lean_closure_set(v___f_937_, 15, v_t_x3f_934_);
if (lean_obj_tag(v_t_x3f_934_) == 1)
{
lean_object* v_val_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_1050_; 
v_val_938_ = lean_ctor_get(v_t_x3f_934_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_t_x3f_934_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_940_ = v_t_x3f_934_;
v_isShared_941_ = v_isSharedCheck_1050_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_val_938_);
lean_dec(v_t_x3f_934_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_1050_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_942_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0));
lean_inc_ref(v___x_930_);
lean_inc_ref(v___x_929_);
lean_inc_ref(v___x_928_);
v___x_943_ = l_Lean_Name_mkStr4(v___x_928_, v___x_929_, v___x_930_, v___x_942_);
lean_inc(v_val_938_);
v___x_944_ = l_Lean_Syntax_isOfKind(v_val_938_, v___x_943_);
lean_dec(v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
lean_del_object(v___x_940_);
lean_dec(v___x_921_);
v___x_945_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1));
lean_inc_ref(v___x_930_);
lean_inc_ref(v___x_929_);
lean_inc_ref(v___x_928_);
v___x_946_ = l_Lean_Name_mkStr4(v___x_928_, v___x_929_, v___x_930_, v___x_945_);
lean_inc(v_val_938_);
v___x_947_ = l_Lean_Syntax_isOfKind(v_val_938_, v___x_946_);
lean_dec(v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_948_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_930_);
lean_inc_ref(v___x_929_);
lean_inc_ref(v___x_928_);
v___x_949_ = l_Lean_Name_mkStr4(v___x_928_, v___x_929_, v___x_930_, v___x_948_);
lean_inc(v_val_938_);
v___x_950_ = l_Lean_Syntax_isOfKind(v_val_938_, v___x_949_);
lean_dec(v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_951_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_930_);
lean_inc_ref(v___x_929_);
lean_inc_ref(v___x_928_);
v___x_952_ = l_Lean_Name_mkStr4(v___x_928_, v___x_929_, v___x_930_, v___x_951_);
lean_inc(v_val_938_);
v___x_953_ = l_Lean_Syntax_isOfKind(v_val_938_, v___x_952_);
lean_dec(v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_954_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_955_ = l_Lean_Name_mkStr4(v___x_928_, v___x_929_, v___x_930_, v___x_954_);
lean_inc(v_val_938_);
v___x_956_ = l_Lean_Syntax_isOfKind(v_val_938_, v___x_955_);
lean_dec(v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___f_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec(v___x_933_);
lean_dec(v_toPure_923_);
v___f_957_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_957_, 0, v___f_937_);
v___x_958_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_959_ = l_Lean_throwErrorAt___redArg(v_inst_931_, v_inst_932_, v_val_938_, v___x_958_);
v___x_960_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_959_, v___f_957_);
return v___x_960_;
}
else
{
lean_object* v___f_961_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___f_961_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_961_, 0, v___f_937_);
v___x_966_ = l_Lean_Syntax_getArg(v_val_938_, v___x_933_);
lean_dec(v___x_933_);
v___x_967_ = l_Lean_Syntax_isNone(v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_968_ = lean_unsigned_to_nat(2u);
v___x_969_ = l_Lean_Syntax_matchesNull(v___x_966_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec(v_toPure_923_);
v___x_970_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_971_ = l_Lean_throwErrorAt___redArg(v_inst_931_, v_inst_932_, v_val_938_, v___x_970_);
v___x_972_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_971_, v___f_961_);
return v___x_972_;
}
else
{
lean_dec(v_val_938_);
lean_dec_ref(v_inst_932_);
lean_dec_ref(v_inst_931_);
goto v___jp_962_;
}
}
else
{
lean_dec(v___x_966_);
lean_dec(v_val_938_);
lean_dec_ref(v_inst_932_);
lean_dec_ref(v_inst_931_);
goto v___jp_962_;
}
v___jp_962_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_963_ = lean_box(0);
v___x_964_ = lean_apply_2(v_toPure_923_, lean_box(0), v___x_963_);
v___x_965_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_964_, v___f_961_);
return v___x_965_;
}
}
}
else
{
lean_object* v___f_973_; lean_object* v___x_978_; uint8_t v___x_979_; 
lean_dec_ref(v___x_930_);
lean_dec_ref(v___x_929_);
lean_dec_ref(v___x_928_);
v___f_973_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_973_, 0, v___f_937_);
v___x_978_ = l_Lean_Syntax_getArg(v_val_938_, v___x_933_);
lean_dec(v___x_933_);
v___x_979_ = l_Lean_Syntax_isNone(v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_unsigned_to_nat(2u);
v___x_981_ = l_Lean_Syntax_matchesNull(v___x_978_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec(v_toPure_923_);
v___x_982_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_983_ = l_Lean_throwErrorAt___redArg(v_inst_931_, v_inst_932_, v_val_938_, v___x_982_);
v___x_984_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_983_, v___f_973_);
return v___x_984_;
}
else
{
lean_dec(v_val_938_);
lean_dec_ref(v_inst_932_);
lean_dec_ref(v_inst_931_);
goto v___jp_974_;
}
}
else
{
lean_dec(v___x_978_);
lean_dec(v_val_938_);
lean_dec_ref(v_inst_932_);
lean_dec_ref(v_inst_931_);
goto v___jp_974_;
}
v___jp_974_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_box(0);
v___x_976_ = lean_apply_2(v_toPure_923_, lean_box(0), v___x_975_);
v___x_977_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_976_, v___f_973_);
return v___x_977_;
}
}
}
else
{
lean_object* v___f_985_; lean_object* v___x_990_; uint8_t v___x_991_; 
lean_dec_ref(v___x_930_);
lean_dec_ref(v___x_929_);
lean_dec_ref(v___x_928_);
v___f_985_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_985_, 0, v___f_937_);
v___x_990_ = l_Lean_Syntax_getArg(v_val_938_, v___x_933_);
lean_dec(v___x_933_);
v___x_991_ = l_Lean_Syntax_isNone(v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = lean_unsigned_to_nat(2u);
v___x_993_ = l_Lean_Syntax_matchesNull(v___x_990_, v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec(v_toPure_923_);
v___x_994_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_995_ = l_Lean_throwErrorAt___redArg(v_inst_931_, v_inst_932_, v_val_938_, v___x_994_);
v___x_996_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_995_, v___f_985_);
return v___x_996_;
}
else
{
lean_dec(v_val_938_);
lean_dec_ref(v_inst_932_);
lean_dec_ref(v_inst_931_);
goto v___jp_986_;
}
}
else
{
lean_dec(v___x_990_);
lean_dec(v_val_938_);
lean_dec_ref(v_inst_932_);
lean_dec_ref(v_inst_931_);
goto v___jp_986_;
}
v___jp_986_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_box(0);
v___x_988_ = lean_apply_2(v_toPure_923_, lean_box(0), v___x_987_);
v___x_989_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_988_, v___f_985_);
return v___x_989_;
}
}
}
else
{
lean_object* v___f_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec(v_val_938_);
lean_dec(v___x_933_);
lean_dec_ref(v_inst_932_);
lean_dec_ref(v_inst_931_);
lean_dec_ref(v___x_930_);
lean_dec_ref(v___x_929_);
lean_dec_ref(v___x_928_);
v___f_997_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_997_, 0, v___f_937_);
v___x_998_ = lean_box(0);
v___x_999_ = lean_apply_2(v_toPure_923_, lean_box(0), v___x_998_);
v___x_1000_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_999_, v___f_997_);
return v___x_1000_;
}
}
else
{
lean_object* v___f_1001_; lean_object* v___y_1003_; uint8_t v___y_1004_; lean_object* v___y_1005_; uint8_t v___y_1006_; lean_object* v___y_1014_; uint8_t v___y_1015_; uint8_t v___y_1016_; lean_object* v_s_1023_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
lean_dec_ref(v___x_930_);
lean_dec_ref(v___x_929_);
lean_dec_ref(v___x_928_);
v___f_1001_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1001_, 0, v___f_937_);
v___x_1041_ = l_Lean_Syntax_getArg(v_val_938_, v___x_933_);
v___x_1042_ = l_Lean_Syntax_isNone(v___x_1041_);
if (v___x_1042_ == 0)
{
uint8_t v___x_1043_; 
lean_inc(v___x_1041_);
v___x_1043_ = l_Lean_Syntax_matchesNull(v___x_1041_, v___x_933_);
lean_dec(v___x_933_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec(v___x_1041_);
lean_del_object(v___x_940_);
lean_dec(v_toPure_923_);
lean_dec(v___x_921_);
v___x_1044_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1045_ = l_Lean_throwErrorAt___redArg(v_inst_931_, v_inst_932_, v_val_938_, v___x_1044_);
v___x_1046_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_1045_, v___f_1001_);
return v___x_1046_;
}
else
{
lean_object* v_s_1047_; lean_object* v___x_1048_; 
v_s_1047_ = l_Lean_Syntax_getArg(v___x_1041_, v___x_921_);
lean_dec(v___x_1041_);
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_s_1047_);
v_s_1023_ = v___x_1048_;
goto v___jp_1022_;
}
}
else
{
lean_object* v___x_1049_; 
lean_dec(v___x_1041_);
lean_dec(v___x_933_);
v___x_1049_ = lean_box(0);
v_s_1023_ = v___x_1049_;
goto v___jp_1022_;
}
v___jp_1002_:
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1007_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1007_, 0, v_val_938_);
lean_ctor_set(v___x_1007_, 1, v___y_1005_);
lean_ctor_set(v___x_1007_, 2, v___y_1003_);
lean_ctor_set_uint8(v___x_1007_, sizeof(void*)*3, v___y_1006_);
lean_ctor_set_uint8(v___x_1007_, sizeof(void*)*3 + 1, v___y_1004_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_1007_);
v___x_1009_ = v___x_940_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_apply_2(v_toPure_923_, lean_box(0), v___x_1009_);
v___x_1011_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_1010_, v___f_1001_);
return v___x_1011_;
}
}
v___jp_1013_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1017_ = lean_mk_empty_array_with_capacity(v___x_921_);
lean_dec(v___x_921_);
v___x_1018_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1018_, 0, v_val_938_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
lean_ctor_set(v___x_1018_, 2, v___y_1014_);
lean_ctor_set_uint8(v___x_1018_, sizeof(void*)*3, v___y_1016_);
lean_ctor_set_uint8(v___x_1018_, sizeof(void*)*3 + 1, v___y_1015_);
v___x_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
v___x_1020_ = lean_apply_2(v_toPure_923_, lean_box(0), v___x_1019_);
v___x_1021_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_1020_, v___f_1001_);
return v___x_1021_;
}
v___jp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1024_ = lean_unsigned_to_nat(2u);
v___x_1025_ = l_Lean_Syntax_getArg(v_val_938_, v___x_1024_);
lean_inc(v___x_1025_);
v___x_1026_ = l_Lean_Syntax_matchesNull(v___x_1025_, v___x_1024_);
if (v___x_1026_ == 0)
{
uint8_t v___x_1027_; 
lean_del_object(v___x_940_);
v___x_1027_ = l_Lean_Syntax_matchesNull(v___x_1025_, v___x_921_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec(v_s_1023_);
lean_dec(v_toPure_923_);
lean_dec(v___x_921_);
v___x_1028_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1029_ = l_Lean_throwErrorAt___redArg(v_inst_931_, v_inst_932_, v_val_938_, v___x_1028_);
v___x_1030_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_1029_, v___f_1001_);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; lean_object* v_body_1032_; 
lean_dec_ref(v_inst_932_);
lean_dec_ref(v_inst_931_);
v___x_1031_ = lean_unsigned_to_nat(3u);
v_body_1032_ = l_Lean_Syntax_getArg(v_val_938_, v___x_1031_);
if (lean_obj_tag(v_s_1023_) == 0)
{
v___y_1014_ = v_body_1032_;
v___y_1015_ = v___x_1026_;
v___y_1016_ = v___x_1026_;
goto v___jp_1013_;
}
else
{
lean_dec_ref_known(v_s_1023_, 1);
v___y_1014_ = v_body_1032_;
v___y_1015_ = v___x_1026_;
v___y_1016_ = v___x_1027_;
goto v___jp_1013_;
}
}
}
else
{
lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = l_Lean_Syntax_getArg(v___x_1025_, v___x_921_);
lean_dec(v___x_1025_);
lean_inc(v___x_1033_);
v___x_1034_ = l_Lean_Syntax_matchesNull(v___x_1033_, v___x_921_);
lean_dec(v___x_921_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v_body_1036_; lean_object* v_vars_1037_; 
lean_dec_ref(v_inst_932_);
lean_dec_ref(v_inst_931_);
v___x_1035_ = lean_unsigned_to_nat(3u);
v_body_1036_ = l_Lean_Syntax_getArg(v_val_938_, v___x_1035_);
v_vars_1037_ = l_Lean_Syntax_getArgs(v___x_1033_);
lean_dec(v___x_1033_);
if (lean_obj_tag(v_s_1023_) == 0)
{
v___y_1003_ = v_body_1036_;
v___y_1004_ = v___x_1034_;
v___y_1005_ = v_vars_1037_;
v___y_1006_ = v___x_1034_;
goto v___jp_1002_;
}
else
{
lean_dec_ref_known(v_s_1023_, 1);
v___y_1003_ = v_body_1036_;
v___y_1004_ = v___x_1034_;
v___y_1005_ = v_vars_1037_;
v___y_1006_ = v___x_1026_;
goto v___jp_1002_;
}
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec(v___x_1033_);
lean_dec(v_s_1023_);
lean_del_object(v___x_940_);
lean_dec(v_toPure_923_);
v___x_1038_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
v___x_1039_ = l_Lean_throwErrorAt___redArg(v_inst_931_, v_inst_932_, v_val_938_, v___x_1038_);
v___x_1040_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_1039_, v___f_1001_);
return v___x_1040_;
}
}
}
}
}
}
else
{
lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v_t_x3f_934_);
lean_dec(v___x_933_);
lean_dec_ref(v_inst_932_);
lean_dec_ref(v_inst_931_);
lean_dec_ref(v___x_930_);
lean_dec_ref(v___x_929_);
lean_dec_ref(v___x_928_);
lean_dec(v___x_921_);
v___f_1051_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1051_, 0, v___f_937_);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_apply_2(v_toPure_923_, lean_box(0), v___x_1052_);
v___x_1054_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_1053_, v___f_1051_);
return v___x_1054_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_elabTerminationHints___redArg___lam__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_920_ = stack[0].m_obj;
lean_object* v___x_921_ = stack[1].m_obj;
uint8_t v___x_922_ = stack[2].m_num;
lean_object* v_toPure_923_ = stack[3].m_obj;
lean_object* v_d_x3f_924_ = stack[4].m_obj;
lean_object* v_toBind_925_ = stack[5].m_obj;
lean_object* v_toFunctor_926_ = stack[6].m_obj;
lean_object* v___f_927_ = stack[7].m_obj;
lean_object* v___x_928_ = stack[8].m_obj;
lean_object* v___x_929_ = stack[9].m_obj;
lean_object* v___x_930_ = stack[10].m_obj;
lean_object* v_inst_931_ = stack[11].m_obj;
lean_object* v_inst_932_ = stack[12].m_obj;
lean_object* v___x_933_ = stack[13].m_obj;
lean_object* v_t_x3f_934_ = stack[14].m_obj;
lean_object* v_terminationBy_x3f_x3f_935_ = stack[15].m_obj;
lean_object* v_res_1055_;
v_res_1055_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19(v_stx_920_, v___x_921_, v___x_922_, v_toPure_923_, v_d_x3f_924_, v_toBind_925_, v_toFunctor_926_, v___f_927_, v___x_928_, v___x_929_, v___x_930_, v_inst_931_, v_inst_932_, v___x_933_, v_t_x3f_934_, v_terminationBy_x3f_x3f_935_);
stack->m_obj
 = v_res_1055_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed(lean_object* v_stx_1056_, lean_object* v___x_1057_, lean_object* v___x_1058_, lean_object* v_toPure_1059_, lean_object* v_d_x3f_1060_, lean_object* v_toBind_1061_, lean_object* v_toFunctor_1062_, lean_object* v___f_1063_, lean_object* v___x_1064_, lean_object* v___x_1065_, lean_object* v___x_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v___x_1069_, lean_object* v_t_x3f_1070_, lean_object* v_terminationBy_x3f_x3f_1071_){
_start:
{
uint8_t v___x_3400__boxed_1072_; lean_object* v_res_1073_; 
v___x_3400__boxed_1072_ = lean_unbox(v___x_1058_);
v_res_1073_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19(v_stx_1056_, v___x_1057_, v___x_3400__boxed_1072_, v_toPure_1059_, v_d_x3f_1060_, v_toBind_1061_, v_toFunctor_1062_, v___f_1063_, v___x_1064_, v___x_1065_, v___x_1066_, v_inst_1067_, v_inst_1068_, v___x_1069_, v_t_x3f_1070_, v_terminationBy_x3f_x3f_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* v___f_1074_, lean_object* v_terminationBy_x3f_x3f_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_apply_1(v___f_1074_, v_terminationBy_x3f_x3f_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_stx_1101_){
_start:
{
if (lean_obj_tag(v_stx_1101_) == 0)
{
lean_object* v_toApplicative_1102_; lean_object* v_toPure_1103_; uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_toApplicative_1102_ = lean_ctor_get(v_inst_1099_, 0);
lean_inc_ref(v_toApplicative_1102_);
lean_dec_ref(v_inst_1100_);
lean_dec_ref(v_inst_1099_);
v_toPure_1103_ = lean_ctor_get(v_toApplicative_1102_, 1);
lean_inc(v_toPure_1103_);
lean_dec_ref(v_toApplicative_1102_);
v___x_1104_ = 1;
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1107_, 0, v_stx_1101_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
lean_ctor_set(v___x_1107_, 2, v___x_1106_);
lean_ctor_set(v___x_1107_, 3, v___x_1106_);
lean_ctor_set(v___x_1107_, 4, v___x_1106_);
lean_ctor_set(v___x_1107_, 5, v___x_1105_);
lean_ctor_set_uint8(v___x_1107_, sizeof(void*)*6, v___x_1104_);
v___x_1108_ = lean_apply_2(v_toPure_1103_, lean_box(0), v___x_1107_);
return v___x_1108_;
}
else
{
lean_object* v_toApplicative_1109_; lean_object* v_toBind_1110_; lean_object* v_toFunctor_1111_; lean_object* v_toPure_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_toApplicative_1109_ = lean_ctor_get(v_inst_1099_, 0);
v_toBind_1110_ = lean_ctor_get(v_inst_1099_, 1);
v_toFunctor_1111_ = lean_ctor_get(v_toApplicative_1109_, 0);
v_toPure_1112_ = lean_ctor_get(v_toApplicative_1109_, 1);
v___x_1113_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__0));
v___x_1114_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__1));
v___x_1115_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__2));
v___x_1116_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__4));
lean_inc(v_stx_1101_);
v___x_1117_ = l_Lean_Syntax_isOfKind(v_stx_1101_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1118_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1119_ = lean_box(0);
lean_inc_n(v_stx_1101_, 2);
v___x_1120_ = l_Lean_Syntax_formatStx(v_stx_1101_, v___x_1119_, v___x_1117_);
v___x_1121_ = l_Std_Format_defWidth;
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = l_Std_Format_pretty(v___x_1120_, v___x_1121_, v___x_1122_, v___x_1122_);
v___x_1124_ = lean_string_append(v___x_1118_, v___x_1123_);
lean_dec_ref(v___x_1123_);
v___x_1125_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1126_ = lean_string_append(v___x_1124_, v___x_1125_);
v___x_1127_ = l_Lean_Syntax_getKind(v_stx_1101_);
v___x_1128_ = 1;
v___x_1129_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1127_, v___x_1128_);
v___x_1130_ = lean_string_append(v___x_1126_, v___x_1129_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
v___x_1132_ = l_Lean_MessageData_ofFormat(v___x_1131_);
v___x_1133_ = l_Lean_throwErrorAt___redArg(v_inst_1099_, v_inst_1100_, v_stx_1101_, v___x_1132_);
return v___x_1133_;
}
else
{
lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v_d_x3f_1140_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v_t_x3f_1171_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___f_1134_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__7));
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1208_ = l_Lean_Syntax_getArg(v_stx_1101_, v___x_1135_);
v___x_1209_ = l_Lean_Syntax_isNone(v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1208_);
v___x_1211_ = l_Lean_Syntax_matchesNull(v___x_1208_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec(v___x_1208_);
v___x_1212_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1213_ = lean_box(0);
lean_inc_n(v_stx_1101_, 2);
v___x_1214_ = l_Lean_Syntax_formatStx(v_stx_1101_, v___x_1213_, v___x_1211_);
v___x_1215_ = l_Std_Format_defWidth;
v___x_1216_ = l_Std_Format_pretty(v___x_1214_, v___x_1215_, v___x_1135_, v___x_1135_);
v___x_1217_ = lean_string_append(v___x_1212_, v___x_1216_);
lean_dec_ref(v___x_1216_);
v___x_1218_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1219_ = lean_string_append(v___x_1217_, v___x_1218_);
v___x_1220_ = l_Lean_Syntax_getKind(v_stx_1101_);
v___x_1221_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1220_, v___x_1117_);
v___x_1222_ = lean_string_append(v___x_1219_, v___x_1221_);
lean_dec_ref(v___x_1221_);
v___x_1223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
v___x_1224_ = l_Lean_MessageData_ofFormat(v___x_1223_);
v___x_1225_ = l_Lean_throwErrorAt___redArg(v_inst_1099_, v_inst_1100_, v_stx_1101_, v___x_1224_);
return v___x_1225_;
}
else
{
lean_object* v_t_x3f_1226_; lean_object* v___x_1227_; 
v_t_x3f_1226_ = l_Lean_Syntax_getArg(v___x_1208_, v___x_1135_);
lean_dec(v___x_1208_);
v___x_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1227_, 0, v_t_x3f_1226_);
v_t_x3f_1171_ = v___x_1227_;
goto v___jp_1170_;
}
}
else
{
lean_object* v___x_1228_; 
lean_dec(v___x_1208_);
v___x_1228_ = lean_box(0);
v_t_x3f_1171_ = v___x_1228_;
goto v___jp_1170_;
}
v___jp_1136_:
{
lean_object* v___x_1141_; lean_object* v___f_1142_; 
v___x_1141_ = lean_box(v___x_1117_);
lean_inc(v_toBind_1110_);
lean_inc(v_toPure_1112_);
v___f_1142_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed), 16, 15);
lean_closure_set(v___f_1142_, 0, v_stx_1101_);
lean_closure_set(v___f_1142_, 1, v___x_1135_);
lean_closure_set(v___f_1142_, 2, v___x_1141_);
lean_closure_set(v___f_1142_, 3, v_toPure_1112_);
lean_closure_set(v___f_1142_, 4, v_d_x3f_1140_);
lean_closure_set(v___f_1142_, 5, v_toBind_1110_);
lean_closure_set(v___f_1142_, 6, v_toFunctor_1111_);
lean_closure_set(v___f_1142_, 7, v___f_1134_);
lean_closure_set(v___f_1142_, 8, v___x_1113_);
lean_closure_set(v___f_1142_, 9, v___x_1114_);
lean_closure_set(v___f_1142_, 10, v___x_1115_);
lean_closure_set(v___f_1142_, 11, v_inst_1099_);
lean_closure_set(v___f_1142_, 12, v_inst_1100_);
lean_closure_set(v___f_1142_, 13, v___y_1137_);
lean_closure_set(v___f_1142_, 14, v___y_1138_);
if (lean_obj_tag(v___y_1139_) == 1)
{
lean_object* v_val_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1159_; 
v_val_1143_ = lean_ctor_get(v___y_1139_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___y_1139_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1145_ = v___y_1139_;
v_isShared_1146_ = v_isSharedCheck_1159_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_val_1143_);
lean_dec(v___y_1139_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1159_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__8));
lean_inc(v_val_1143_);
v___x_1148_ = l_Lean_Syntax_isOfKind(v_val_1143_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___f_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_del_object(v___x_1145_);
lean_dec(v_val_1143_);
v___f_1149_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1149_, 0, v___f_1142_);
v___x_1150_ = lean_box(0);
v___x_1151_ = lean_apply_2(v_toPure_1112_, lean_box(0), v___x_1150_);
v___x_1152_ = lean_apply_4(v_toBind_1110_, lean_box(0), lean_box(0), v___x_1151_, v___f_1149_);
return v___x_1152_;
}
else
{
lean_object* v___f_1153_; lean_object* v___x_1155_; 
v___f_1153_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1153_, 0, v___f_1142_);
if (v_isShared_1146_ == 0)
{
v___x_1155_ = v___x_1145_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_val_1143_);
v___x_1155_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_apply_2(v_toPure_1112_, lean_box(0), v___x_1155_);
v___x_1157_ = lean_apply_4(v_toBind_1110_, lean_box(0), lean_box(0), v___x_1156_, v___f_1153_);
return v___x_1157_;
}
}
}
}
else
{
lean_object* v___f_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec(v___y_1139_);
v___f_1160_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1160_, 0, v___f_1142_);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_apply_2(v_toPure_1112_, lean_box(0), v___x_1161_);
v___x_1163_ = lean_apply_4(v_toBind_1110_, lean_box(0), lean_box(0), v___x_1162_, v___f_1160_);
return v___x_1163_;
}
}
v___jp_1164_:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___y_1167_);
v___y_1137_ = v___y_1165_;
v___y_1138_ = v___y_1166_;
v___y_1139_ = v___y_1168_;
v_d_x3f_1140_ = v___x_1169_;
goto v___jp_1136_;
}
v___jp_1170_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = l_Lean_Syntax_getArg(v_stx_1101_, v___x_1172_);
v___x_1174_ = l_Lean_Syntax_isNone(v___x_1173_);
if (v___x_1174_ == 0)
{
uint8_t v___x_1175_; 
lean_inc(v___x_1173_);
v___x_1175_ = l_Lean_Syntax_matchesNull(v___x_1173_, v___x_1172_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec(v___x_1173_);
lean_dec(v_t_x3f_1171_);
v___x_1176_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1177_ = lean_box(0);
lean_inc_n(v_stx_1101_, 2);
v___x_1178_ = l_Lean_Syntax_formatStx(v_stx_1101_, v___x_1177_, v___x_1175_);
v___x_1179_ = l_Std_Format_defWidth;
v___x_1180_ = l_Std_Format_pretty(v___x_1178_, v___x_1179_, v___x_1135_, v___x_1135_);
v___x_1181_ = lean_string_append(v___x_1176_, v___x_1180_);
lean_dec_ref(v___x_1180_);
v___x_1182_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1183_ = lean_string_append(v___x_1181_, v___x_1182_);
v___x_1184_ = l_Lean_Syntax_getKind(v_stx_1101_);
v___x_1185_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1184_, v___x_1117_);
v___x_1186_ = lean_string_append(v___x_1183_, v___x_1185_);
lean_dec_ref(v___x_1185_);
v___x_1187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
v___x_1188_ = l_Lean_MessageData_ofFormat(v___x_1187_);
v___x_1189_ = l_Lean_throwErrorAt___redArg(v_inst_1099_, v_inst_1100_, v_stx_1101_, v___x_1188_);
return v___x_1189_;
}
else
{
lean_object* v_d_x3f_1190_; 
v_d_x3f_1190_ = l_Lean_Syntax_getArg(v___x_1173_, v___x_1135_);
lean_dec(v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__9));
lean_inc(v_d_x3f_1190_);
v___x_1192_ = l_Lean_Syntax_isOfKind(v_d_x3f_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v_d_x3f_1190_);
lean_dec(v_t_x3f_1171_);
v___x_1193_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1194_ = lean_box(0);
lean_inc_n(v_stx_1101_, 2);
v___x_1195_ = l_Lean_Syntax_formatStx(v_stx_1101_, v___x_1194_, v___x_1174_);
v___x_1196_ = l_Std_Format_defWidth;
v___x_1197_ = l_Std_Format_pretty(v___x_1195_, v___x_1196_, v___x_1135_, v___x_1135_);
v___x_1198_ = lean_string_append(v___x_1193_, v___x_1197_);
lean_dec_ref(v___x_1197_);
v___x_1199_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1200_ = lean_string_append(v___x_1198_, v___x_1199_);
v___x_1201_ = l_Lean_Syntax_getKind(v_stx_1101_);
v___x_1202_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1201_, v___x_1175_);
v___x_1203_ = lean_string_append(v___x_1200_, v___x_1202_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
v___x_1205_ = l_Lean_MessageData_ofFormat(v___x_1204_);
v___x_1206_ = l_Lean_throwErrorAt___redArg(v_inst_1099_, v_inst_1100_, v_stx_1101_, v___x_1205_);
return v___x_1206_;
}
else
{
lean_inc(v_toPure_1112_);
lean_inc_ref(v_toFunctor_1111_);
lean_inc(v_toBind_1110_);
lean_inc(v_t_x3f_1171_);
v___y_1165_ = v___x_1172_;
v___y_1166_ = v_t_x3f_1171_;
v___y_1167_ = v_d_x3f_1190_;
v___y_1168_ = v_t_x3f_1171_;
goto v___jp_1164_;
}
}
else
{
lean_inc(v_toPure_1112_);
lean_inc_ref(v_toFunctor_1111_);
lean_inc(v_toBind_1110_);
lean_inc(v_t_x3f_1171_);
v___y_1165_ = v___x_1172_;
v___y_1166_ = v_t_x3f_1171_;
v___y_1167_ = v_d_x3f_1190_;
v___y_1168_ = v_t_x3f_1171_;
goto v___jp_1164_;
}
}
}
else
{
lean_object* v___x_1207_; 
lean_inc(v_toPure_1112_);
lean_inc_ref(v_toFunctor_1111_);
lean_inc(v_toBind_1110_);
lean_dec(v___x_1173_);
v___x_1207_ = lean_box(0);
lean_inc(v_t_x3f_1171_);
v___y_1137_ = v___x_1172_;
v___y_1138_ = v_t_x3f_1171_;
v___y_1139_ = v_t_x3f_1171_;
v_d_x3f_1140_ = v___x_1207_;
goto v___jp_1136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* v_m_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_stx_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_Elab_elabTerminationHints___redArg(v_inst_1230_, v_inst_1231_, v_stx_1232_);
return v___x_1233_;
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
