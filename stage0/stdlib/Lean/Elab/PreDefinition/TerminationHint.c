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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 1)
{
lean_object* v_pre_167_; 
v_pre_167_ = lean_ctor_get(v_x_166_, 0);
switch(lean_obj_tag(v_pre_167_))
{
case 1:
{
lean_object* v_pre_168_; 
v_pre_168_ = lean_ctor_get(v_pre_167_, 0);
switch(lean_obj_tag(v_pre_168_))
{
case 0:
{
lean_object* v_str_169_; lean_object* v_str_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v_str_169_ = lean_ctor_get(v_x_166_, 1);
v_str_170_ = lean_ctor_get(v_pre_167_, 1);
v___x_171_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0));
v___x_172_ = lean_string_dec_eq(v_str_170_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1));
v___x_174_ = lean_string_dec_eq(v_str_170_, v___x_173_);
if (v___x_174_ == 0)
{
return v___x_174_;
}
else
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2));
v___x_176_ = lean_string_dec_eq(v_str_169_, v___x_175_);
if (v___x_176_ == 0)
{
return v___x_176_;
}
else
{
return v_suppressElabErrors_165_;
}
}
}
else
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3));
v___x_178_ = lean_string_dec_eq(v_str_169_, v___x_177_);
if (v___x_178_ == 0)
{
return v___x_178_;
}
else
{
return v_suppressElabErrors_165_;
}
}
}
case 1:
{
lean_object* v_pre_179_; 
v_pre_179_ = lean_ctor_get(v_pre_168_, 0);
if (lean_obj_tag(v_pre_179_) == 0)
{
lean_object* v_str_180_; lean_object* v_str_181_; lean_object* v_str_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_str_180_ = lean_ctor_get(v_x_166_, 1);
v_str_181_ = lean_ctor_get(v_pre_167_, 1);
v_str_182_ = lean_ctor_get(v_pre_168_, 1);
v___x_183_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4));
v___x_184_ = lean_string_dec_eq(v_str_182_, v___x_183_);
if (v___x_184_ == 0)
{
return v___x_184_;
}
else
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5));
v___x_186_ = lean_string_dec_eq(v_str_181_, v___x_185_);
if (v___x_186_ == 0)
{
return v___x_186_;
}
else
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6));
v___x_188_ = lean_string_dec_eq(v_str_180_, v___x_187_);
if (v___x_188_ == 0)
{
return v___x_188_;
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
uint8_t v___x_189_; 
v___x_189_ = 0;
return v___x_189_;
}
}
default: 
{
uint8_t v___x_190_; 
v___x_190_ = 0;
return v___x_190_;
}
}
}
case 0:
{
lean_object* v_str_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_str_191_ = lean_ctor_get(v_x_166_, 1);
v___x_192_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7));
v___x_193_ = lean_string_dec_eq(v_str_191_, v___x_192_);
if (v___x_193_ == 0)
{
return v___x_193_;
}
else
{
return v_suppressElabErrors_165_;
}
}
default: 
{
uint8_t v___x_194_; 
v___x_194_ = 0;
return v___x_194_;
}
}
}
else
{
uint8_t v___x_195_; 
v___x_195_ = 0;
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_196_, lean_object* v_x_197_){
_start:
{
uint8_t v_suppressElabErrors_boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v_suppressElabErrors_boxed_198_ = lean_unbox(v_suppressElabErrors_196_);
v_res_199_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_198_, v_x_197_);
lean_dec(v_x_197_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(lean_object* v_opts_201_, lean_object* v_opt_202_){
_start:
{
lean_object* v_name_203_; lean_object* v_defValue_204_; lean_object* v_map_205_; lean_object* v___x_206_; 
v_name_203_ = lean_ctor_get(v_opt_202_, 0);
v_defValue_204_ = lean_ctor_get(v_opt_202_, 1);
v_map_205_ = lean_ctor_get(v_opts_201_, 0);
v___x_206_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_205_, v_name_203_);
if (lean_obj_tag(v___x_206_) == 0)
{
uint8_t v___x_207_; 
v___x_207_ = lean_unbox(v_defValue_204_);
return v___x_207_;
}
else
{
lean_object* v_val_208_; 
v_val_208_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v___x_206_, 1);
if (lean_obj_tag(v_val_208_) == 1)
{
uint8_t v_v_209_; 
v_v_209_ = lean_ctor_get_uint8(v_val_208_, 0);
lean_dec_ref_known(v_val_208_, 0);
return v_v_209_;
}
else
{
uint8_t v___x_210_; 
lean_dec(v_val_208_);
v___x_210_ = lean_unbox(v_defValue_204_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_211_, lean_object* v_opt_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_opts_211_, v_opt_212_);
lean_dec_ref(v_opt_212_);
lean_dec_ref(v_opts_211_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(lean_object* v_ref_216_, lean_object* v_msgData_217_, uint8_t v_severity_218_, uint8_t v_isSilent_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; uint8_t v___y_228_; uint8_t v___y_229_; lean_object* v___y_230_; lean_object* v_toCold_231_; lean_object* v___y_232_; lean_object* v___y_261_; lean_object* v___y_262_; uint8_t v___y_263_; lean_object* v___y_264_; uint8_t v___y_265_; uint8_t v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_288_; uint8_t v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; uint8_t v___y_292_; uint8_t v___y_293_; lean_object* v___y_294_; uint8_t v___y_298_; uint8_t v___y_299_; uint8_t v___x_309_; uint8_t v___y_311_; uint8_t v___x_317_; 
v___x_309_ = 2;
v___x_317_ = l_Lean_instBEqMessageSeverity_beq(v_severity_218_, v___x_309_);
if (v___x_317_ == 0)
{
v___y_311_ = v___x_317_;
goto v___jp_310_;
}
else
{
uint8_t v___x_318_; 
lean_inc_ref(v_msgData_217_);
v___x_318_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_217_);
if (v___x_318_ == 0)
{
v___y_311_ = v___x_318_;
goto v___jp_310_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_msgData_217_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
v___jp_223_:
{
lean_object* v_currNamespace_233_; lean_object* v_openDecls_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v_env_239_; lean_object* v_nextMacroScope_240_; lean_object* v_ngen_241_; lean_object* v_auxDeclNGen_242_; lean_object* v_traceState_243_; lean_object* v_cache_244_; lean_object* v_recordedDeps_245_; lean_object* v_messages_246_; lean_object* v_infoState_247_; lean_object* v_snapshotTasks_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_259_; 
v_currNamespace_233_ = lean_ctor_get(v_toCold_231_, 4);
v_openDecls_234_ = lean_ctor_get(v_toCold_231_, 5);
lean_inc(v_openDecls_234_);
lean_inc(v_currNamespace_233_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_currNamespace_233_);
lean_ctor_set(v___x_235_, 1, v_openDecls_234_);
v___x_236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___y_226_);
lean_inc_ref(v___y_225_);
lean_inc_ref(v___y_227_);
v___x_237_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_237_, 0, v___y_227_);
lean_ctor_set(v___x_237_, 1, v___y_230_);
lean_ctor_set(v___x_237_, 2, v___y_224_);
lean_ctor_set(v___x_237_, 3, v___y_225_);
lean_ctor_set(v___x_237_, 4, v___x_236_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*5, v___y_229_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*5 + 1, v___y_228_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*5 + 2, v_isSilent_219_);
v___x_238_ = lean_st_ref_take(v___y_232_);
v_env_239_ = lean_ctor_get(v___x_238_, 0);
v_nextMacroScope_240_ = lean_ctor_get(v___x_238_, 1);
v_ngen_241_ = lean_ctor_get(v___x_238_, 2);
v_auxDeclNGen_242_ = lean_ctor_get(v___x_238_, 3);
v_traceState_243_ = lean_ctor_get(v___x_238_, 4);
v_cache_244_ = lean_ctor_get(v___x_238_, 5);
v_recordedDeps_245_ = lean_ctor_get(v___x_238_, 6);
v_messages_246_ = lean_ctor_get(v___x_238_, 7);
v_infoState_247_ = lean_ctor_get(v___x_238_, 8);
v_snapshotTasks_248_ = lean_ctor_get(v___x_238_, 9);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_259_ == 0)
{
v___x_250_ = v___x_238_;
v_isShared_251_ = v_isSharedCheck_259_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_snapshotTasks_248_);
lean_inc(v_infoState_247_);
lean_inc(v_messages_246_);
lean_inc(v_recordedDeps_245_);
lean_inc(v_cache_244_);
lean_inc(v_traceState_243_);
lean_inc(v_auxDeclNGen_242_);
lean_inc(v_ngen_241_);
lean_inc(v_nextMacroScope_240_);
lean_inc(v_env_239_);
lean_dec(v___x_238_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_259_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_252_ = lean_box(0);
v___x_253_ = l_Lean_MessageLog_add(v___x_237_, v_messages_246_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 7, v___x_253_);
v___x_255_ = v___x_250_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_env_239_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_nextMacroScope_240_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_ngen_241_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_auxDeclNGen_242_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_traceState_243_);
lean_ctor_set(v_reuseFailAlloc_258_, 5, v_cache_244_);
lean_ctor_set(v_reuseFailAlloc_258_, 6, v_recordedDeps_245_);
lean_ctor_set(v_reuseFailAlloc_258_, 7, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_258_, 8, v_infoState_247_);
lean_ctor_set(v_reuseFailAlloc_258_, 9, v_snapshotTasks_248_);
v___x_255_ = v_reuseFailAlloc_258_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_st_ref_put(v___y_232_, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_252_);
return v___x_257_;
}
}
}
v___jp_260_:
{
lean_object* v_fileName_269_; lean_object* v_fileMap_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_286_; 
v_fileName_269_ = lean_ctor_get(v___y_267_, 0);
v_fileMap_270_ = lean_ctor_get(v___y_267_, 1);
v___x_271_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_217_);
v___x_272_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v___x_271_, v___y_220_, v___y_221_);
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_286_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_286_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_286_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
lean_inc_ref_n(v_fileMap_270_, 2);
v___x_277_ = l_Lean_FileMap_toPosition(v_fileMap_270_, v___y_264_);
lean_dec(v___y_264_);
v___x_278_ = l_Lean_FileMap_toPosition(v_fileMap_270_, v___y_268_);
lean_dec(v___y_268_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
v___x_280_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0));
if (v___y_263_ == 0)
{
lean_del_object(v___x_275_);
lean_dec_ref(v___y_261_);
v___y_224_ = v___x_279_;
v___y_225_ = v___x_280_;
v___y_226_ = v_a_273_;
v___y_227_ = v_fileName_269_;
v___y_228_ = v___y_266_;
v___y_229_ = v___y_265_;
v___y_230_ = v___x_277_;
v_toCold_231_ = v___y_262_;
v___y_232_ = v___y_221_;
goto v___jp_223_;
}
else
{
uint8_t v___x_281_; 
lean_inc(v_a_273_);
v___x_281_ = l_Lean_MessageData_hasTag(v___y_261_, v_a_273_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_284_; 
lean_dec_ref_known(v___x_279_, 1);
lean_dec_ref(v___x_277_);
lean_dec(v_a_273_);
v___x_282_ = lean_box(0);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_282_);
v___x_284_ = v___x_275_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
else
{
lean_del_object(v___x_275_);
v___y_224_ = v___x_279_;
v___y_225_ = v___x_280_;
v___y_226_ = v_a_273_;
v___y_227_ = v_fileName_269_;
v___y_228_ = v___y_266_;
v___y_229_ = v___y_265_;
v___y_230_ = v___x_277_;
v_toCold_231_ = v___y_262_;
v___y_232_ = v___y_221_;
goto v___jp_223_;
}
}
}
}
v___jp_287_:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Syntax_getTailPos_x3f(v___y_291_, v___y_293_);
lean_dec(v___y_291_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_inc(v___y_294_);
v___y_261_ = v___y_288_;
v___y_262_ = v___y_290_;
v___y_263_ = v___y_289_;
v___y_264_ = v___y_294_;
v___y_265_ = v___y_293_;
v___y_266_ = v___y_292_;
v___y_267_ = v___y_290_;
v___y_268_ = v___y_294_;
goto v___jp_260_;
}
else
{
lean_object* v_val_296_; 
v_val_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_val_296_);
lean_dec_ref_known(v___x_295_, 1);
v___y_261_ = v___y_288_;
v___y_262_ = v___y_290_;
v___y_263_ = v___y_289_;
v___y_264_ = v___y_294_;
v___y_265_ = v___y_293_;
v___y_266_ = v___y_292_;
v___y_267_ = v___y_290_;
v___y_268_ = v_val_296_;
goto v___jp_260_;
}
}
v___jp_297_:
{
lean_object* v_toCold_300_; lean_object* v_ref_301_; uint8_t v_suppressElabErrors_302_; lean_object* v___x_303_; lean_object* v___f_304_; lean_object* v_ref_305_; lean_object* v___x_306_; 
v_toCold_300_ = lean_ctor_get(v___y_220_, 0);
v_ref_301_ = lean_ctor_get(v___y_220_, 2);
v_suppressElabErrors_302_ = lean_ctor_get_uint8(v___y_220_, sizeof(void*)*3 + 2);
v___x_303_ = lean_box(v_suppressElabErrors_302_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_304_, 0, v___x_303_);
v_ref_305_ = l_Lean_replaceRef(v_ref_216_, v_ref_301_);
v___x_306_ = l_Lean_Syntax_getPos_x3f(v_ref_305_, v___y_298_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___y_288_ = v___f_304_;
v___y_289_ = v_suppressElabErrors_302_;
v___y_290_ = v_toCold_300_;
v___y_291_ = v_ref_305_;
v___y_292_ = v___y_299_;
v___y_293_ = v___y_298_;
v___y_294_ = v___x_307_;
goto v___jp_287_;
}
else
{
lean_object* v_val_308_; 
v_val_308_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v___x_306_, 1);
v___y_288_ = v___f_304_;
v___y_289_ = v_suppressElabErrors_302_;
v___y_290_ = v_toCold_300_;
v___y_291_ = v_ref_305_;
v___y_292_ = v___y_299_;
v___y_293_ = v___y_298_;
v___y_294_ = v_val_308_;
goto v___jp_287_;
}
}
v___jp_310_:
{
uint8_t v___x_312_; uint8_t v___x_313_; 
v___x_312_ = 1;
v___x_313_ = l_Lean_instBEqMessageSeverity_beq(v_severity_218_, v___x_312_);
if (v___x_313_ == 0)
{
v___y_298_ = v___y_311_;
v___y_299_ = v_severity_218_;
goto v___jp_297_;
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_220_);
v___x_315_ = l_Lean_warningAsError;
v___x_316_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v___x_314_, v___x_315_);
lean_dec_ref(v___x_314_);
if (v___x_316_ == 0)
{
v___y_298_ = v___y_311_;
v___y_299_ = v_severity_218_;
goto v___jp_297_;
}
else
{
v___y_298_ = v___y_311_;
v___y_299_ = v___x_309_;
goto v___jp_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___boxed(lean_object* v_ref_321_, lean_object* v_msgData_322_, lean_object* v_severity_323_, lean_object* v_isSilent_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
uint8_t v_severity_boxed_328_; uint8_t v_isSilent_boxed_329_; lean_object* v_res_330_; 
v_severity_boxed_328_ = lean_unbox(v_severity_323_);
v_isSilent_boxed_329_ = lean_unbox(v_isSilent_324_);
v_res_330_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_321_, v_msgData_322_, v_severity_boxed_328_, v_isSilent_boxed_329_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v_ref_321_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(lean_object* v_ref_331_, lean_object* v_msgData_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
uint8_t v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; 
v___x_336_ = 1;
v___x_337_ = 0;
v___x_338_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_331_, v_msgData_332_, v___x_336_, v___x_337_, v___y_333_, v___y_334_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(lean_object* v_ref_339_, lean_object* v_msgData_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_339_, v_msgData_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v_ref_339_);
return v_res_344_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__0));
v___x_347_ = l_Lean_stringToMessageData(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__2));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__4));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__6));
v___x_356_ = l_Lean_stringToMessageData(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__8));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__10));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__12));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone(lean_object* v_hints_366_, lean_object* v_reason_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_ref_371_; lean_object* v_terminationBy_x3f_x3f_372_; lean_object* v_terminationBy_x3f_373_; lean_object* v_partialFixpoint_x3f_374_; lean_object* v_decreasingBy_x3f_375_; uint8_t v_warnIfRedundant_376_; lean_object* v___y_378_; lean_object* v___y_379_; 
v_ref_371_ = lean_ctor_get(v_hints_366_, 0);
lean_inc(v_ref_371_);
v_terminationBy_x3f_x3f_372_ = lean_ctor_get(v_hints_366_, 1);
lean_inc(v_terminationBy_x3f_x3f_372_);
v_terminationBy_x3f_373_ = lean_ctor_get(v_hints_366_, 2);
lean_inc(v_terminationBy_x3f_373_);
v_partialFixpoint_x3f_374_ = lean_ctor_get(v_hints_366_, 3);
lean_inc(v_partialFixpoint_x3f_374_);
v_decreasingBy_x3f_375_ = lean_ctor_get(v_hints_366_, 4);
lean_inc(v_decreasingBy_x3f_375_);
v_warnIfRedundant_376_ = lean_ctor_get_uint8(v_hints_366_, sizeof(void*)*6);
lean_dec_ref(v_hints_366_);
if (v_warnIfRedundant_376_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v_decreasingBy_x3f_375_);
lean_dec(v_partialFixpoint_x3f_374_);
lean_dec(v_terminationBy_x3f_373_);
lean_dec(v_terminationBy_x3f_x3f_372_);
lean_dec(v_ref_371_);
lean_dec_ref(v_reason_367_);
v___x_384_ = lean_box(0);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_x3f_372_) == 0)
{
if (lean_obj_tag(v_terminationBy_x3f_373_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_375_) == 0)
{
lean_dec(v_ref_371_);
if (lean_obj_tag(v_partialFixpoint_x3f_374_) == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec_ref(v_reason_367_);
v___x_386_ = lean_box(0);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
else
{
lean_object* v_val_388_; uint8_t v_fixpointType_389_; 
v_val_388_ = lean_ctor_get(v_partialFixpoint_x3f_374_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v_partialFixpoint_x3f_374_, 1);
v_fixpointType_389_ = lean_ctor_get_uint8(v_val_388_, sizeof(void*)*2);
switch(v_fixpointType_389_)
{
case 0:
{
lean_object* v_ref_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_ref_390_ = lean_ctor_get(v_val_388_, 0);
lean_inc(v_ref_390_);
lean_dec(v_val_388_);
v___x_391_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__3, &l_Lean_Elab_TerminationHints_ensureNone___closed__3_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3);
v___x_392_ = l_Lean_stringToMessageData(v_reason_367_);
v___x_393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_391_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_390_, v___x_393_, v_a_368_, v_a_369_);
lean_dec(v_ref_390_);
return v___x_394_;
}
case 1:
{
lean_object* v_ref_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_ref_395_ = lean_ctor_get(v_val_388_, 0);
lean_inc(v_ref_395_);
lean_dec(v_val_388_);
v___x_396_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__5, &l_Lean_Elab_TerminationHints_ensureNone___closed__5_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5);
v___x_397_ = l_Lean_stringToMessageData(v_reason_367_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_395_, v___x_398_, v_a_368_, v_a_369_);
lean_dec(v_ref_395_);
return v___x_399_;
}
default: 
{
lean_object* v_ref_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_ref_400_ = lean_ctor_get(v_val_388_, 0);
lean_inc(v_ref_400_);
lean_dec(v_val_388_);
v___x_401_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__7, &l_Lean_Elab_TerminationHints_ensureNone___closed__7_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7);
v___x_402_ = l_Lean_stringToMessageData(v_reason_367_);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_400_, v___x_403_, v_a_368_, v_a_369_);
lean_dec(v_ref_400_);
return v___x_404_;
}
}
}
}
else
{
if (lean_obj_tag(v_partialFixpoint_x3f_374_) == 0)
{
lean_object* v_val_405_; lean_object* v_ref_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_416_; 
lean_dec(v_ref_371_);
v_val_405_ = lean_ctor_get(v_decreasingBy_x3f_375_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v_decreasingBy_x3f_375_, 1);
v_ref_406_ = lean_ctor_get(v_val_405_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v_val_405_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; 
v_unused_417_ = lean_ctor_get(v_val_405_, 1);
lean_dec(v_unused_417_);
v___x_408_ = v_val_405_;
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_ref_406_);
lean_dec(v_val_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_410_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__9, &l_Lean_Elab_TerminationHints_ensureNone___closed__9_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9);
v___x_411_ = l_Lean_stringToMessageData(v_reason_367_);
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 7);
lean_ctor_set(v___x_408_, 1, v___x_411_);
lean_ctor_set(v___x_408_, 0, v___x_410_);
v___x_413_ = v___x_408_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_411_);
v___x_413_ = v_reuseFailAlloc_415_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_406_, v___x_413_, v_a_368_, v_a_369_);
lean_dec(v_ref_406_);
return v___x_414_;
}
}
}
else
{
lean_dec_ref_known(v_decreasingBy_x3f_375_, 1);
lean_dec(v_partialFixpoint_x3f_374_);
v___y_378_ = v_a_368_;
v___y_379_ = v_a_369_;
goto v___jp_377_;
}
}
}
else
{
if (lean_obj_tag(v_decreasingBy_x3f_375_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_374_) == 0)
{
lean_object* v_val_418_; lean_object* v_ref_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v_ref_371_);
v_val_418_ = lean_ctor_get(v_terminationBy_x3f_373_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v_terminationBy_x3f_373_, 1);
v_ref_419_ = lean_ctor_get(v_val_418_, 0);
lean_inc(v_ref_419_);
lean_dec(v_val_418_);
v___x_420_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__11, &l_Lean_Elab_TerminationHints_ensureNone___closed__11_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11);
v___x_421_ = l_Lean_stringToMessageData(v_reason_367_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_419_, v___x_422_, v_a_368_, v_a_369_);
lean_dec(v_ref_419_);
return v___x_423_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_373_, 1);
lean_dec(v_partialFixpoint_x3f_374_);
v___y_378_ = v_a_368_;
v___y_379_ = v_a_369_;
goto v___jp_377_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_373_, 1);
lean_dec(v_decreasingBy_x3f_375_);
lean_dec(v_partialFixpoint_x3f_374_);
v___y_378_ = v_a_368_;
v___y_379_ = v_a_369_;
goto v___jp_377_;
}
}
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_373_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_375_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_374_) == 0)
{
lean_object* v_val_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_ref_371_);
v_val_424_ = lean_ctor_get(v_terminationBy_x3f_x3f_372_, 0);
lean_inc(v_val_424_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_372_, 1);
v___x_425_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__13, &l_Lean_Elab_TerminationHints_ensureNone___closed__13_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13);
v___x_426_ = l_Lean_stringToMessageData(v_reason_367_);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_val_424_, v___x_427_, v_a_368_, v_a_369_);
lean_dec(v_val_424_);
return v___x_428_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_372_, 1);
lean_dec(v_partialFixpoint_x3f_374_);
v___y_378_ = v_a_368_;
v___y_379_ = v_a_369_;
goto v___jp_377_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_372_, 1);
lean_dec(v_decreasingBy_x3f_375_);
lean_dec(v_partialFixpoint_x3f_374_);
v___y_378_ = v_a_368_;
v___y_379_ = v_a_369_;
goto v___jp_377_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_372_, 1);
lean_dec(v_decreasingBy_x3f_375_);
lean_dec(v_partialFixpoint_x3f_374_);
lean_dec(v_terminationBy_x3f_373_);
v___y_378_ = v_a_368_;
v___y_379_ = v_a_369_;
goto v___jp_377_;
}
}
}
v___jp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_380_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__1, &l_Lean_Elab_TerminationHints_ensureNone___closed__1_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1);
v___x_381_ = l_Lean_stringToMessageData(v_reason_367_);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_371_, v___x_382_, v___y_378_, v___y_379_);
lean_dec(v_ref_371_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone___boxed(lean_object* v_hints_429_, lean_object* v_reason_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Elab_TerminationHints_ensureNone(v_hints_429_, v_reason_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_434_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_TerminationHints_isNotNone(lean_object* v_hints_435_){
_start:
{
lean_object* v_terminationBy_x3f_x3f_436_; 
v_terminationBy_x3f_x3f_436_ = lean_ctor_get(v_hints_435_, 1);
if (lean_obj_tag(v_terminationBy_x3f_x3f_436_) == 0)
{
lean_object* v_terminationBy_x3f_437_; 
v_terminationBy_x3f_437_ = lean_ctor_get(v_hints_435_, 2);
if (lean_obj_tag(v_terminationBy_x3f_437_) == 0)
{
lean_object* v_decreasingBy_x3f_438_; 
v_decreasingBy_x3f_438_ = lean_ctor_get(v_hints_435_, 4);
if (lean_obj_tag(v_decreasingBy_x3f_438_) == 0)
{
lean_object* v_partialFixpoint_x3f_439_; 
v_partialFixpoint_x3f_439_ = lean_ctor_get(v_hints_435_, 3);
if (lean_obj_tag(v_partialFixpoint_x3f_439_) == 0)
{
uint8_t v___x_440_; 
v___x_440_ = 0;
return v___x_440_;
}
else
{
uint8_t v___x_441_; 
v___x_441_ = 1;
return v___x_441_;
}
}
else
{
uint8_t v___x_442_; 
v___x_442_ = 1;
return v___x_442_;
}
}
else
{
uint8_t v___x_443_; 
v___x_443_ = 1;
return v___x_443_;
}
}
else
{
uint8_t v___x_444_; 
v___x_444_ = 1;
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_isNotNone___boxed(lean_object* v_hints_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Lean_Elab_TerminationHints_isNotNone(v_hints_445_);
lean_dec_ref(v_hints_445_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object* v_headerParams_448_, lean_object* v_hints_449_, lean_object* v_value_450_){
_start:
{
lean_object* v_ref_451_; lean_object* v_terminationBy_x3f_x3f_452_; lean_object* v_terminationBy_x3f_453_; lean_object* v_partialFixpoint_x3f_454_; lean_object* v_decreasingBy_x3f_455_; uint8_t v_warnIfRedundant_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_465_; 
v_ref_451_ = lean_ctor_get(v_hints_449_, 0);
v_terminationBy_x3f_x3f_452_ = lean_ctor_get(v_hints_449_, 1);
v_terminationBy_x3f_453_ = lean_ctor_get(v_hints_449_, 2);
v_partialFixpoint_x3f_454_ = lean_ctor_get(v_hints_449_, 3);
v_decreasingBy_x3f_455_ = lean_ctor_get(v_hints_449_, 4);
v_warnIfRedundant_456_ = lean_ctor_get_uint8(v_hints_449_, sizeof(void*)*6);
v_isSharedCheck_465_ = !lean_is_exclusive(v_hints_449_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_hints_449_, 5);
lean_dec(v_unused_466_);
v___x_458_ = v_hints_449_;
v_isShared_459_ = v_isSharedCheck_465_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_decreasingBy_x3f_455_);
lean_inc(v_partialFixpoint_x3f_454_);
lean_inc(v_terminationBy_x3f_453_);
lean_inc(v_terminationBy_x3f_x3f_452_);
lean_inc(v_ref_451_);
lean_dec(v_hints_449_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_465_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_460_ = l_Lean_Expr_getNumHeadLambdas(v_value_450_);
v___x_461_ = lean_nat_sub(v___x_460_, v_headerParams_448_);
lean_dec(v___x_460_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 5, v___x_461_);
v___x_463_ = v___x_458_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_ref_451_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_terminationBy_x3f_x3f_452_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_terminationBy_x3f_453_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_partialFixpoint_x3f_454_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_decreasingBy_x3f_455_);
lean_ctor_set(v_reuseFailAlloc_464_, 5, v___x_461_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*6, v_warnIfRedundant_456_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(lean_object* v_headerParams_467_, lean_object* v_hints_468_, lean_object* v_value_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v_headerParams_467_, v_hints_468_, v_value_469_);
lean_dec_ref(v_value_469_);
lean_dec(v_headerParams_467_);
return v_res_470_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0));
v___x_473_ = l_Lean_stringToMessageData(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3));
v___x_478_ = l_Lean_MessageData_ofFormat(v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(lean_object* v_a_479_){
_start:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_dec_eq(v_a_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_482_ = l_Nat_reprFast(v_a_479_);
v___x_483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
v___x_484_ = l_Lean_MessageData_ofFormat(v___x_483_);
v___x_485_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; 
lean_dec(v_a_479_);
v___x_487_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(lean_object* v_msgData_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; lean_object* v_env_495_; uint8_t v___x_496_; lean_object* v_env_497_; lean_object* v___x_498_; lean_object* v_toCold_499_; lean_object* v_mctx_500_; lean_object* v_lctx_501_; lean_object* v_options_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_494_ = lean_st_ref_get(v___y_492_);
v_env_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc_ref(v_env_495_);
lean_dec(v___x_494_);
v___x_496_ = 0;
v_env_497_ = l_Lean_Environment_setRecordingDeps(v_env_495_, v___x_496_);
v___x_498_ = lean_st_ref_get(v___y_490_);
v_toCold_499_ = lean_ctor_get(v___y_491_, 0);
v_mctx_500_ = lean_ctor_get(v___x_498_, 0);
lean_inc_ref(v_mctx_500_);
lean_dec(v___x_498_);
v_lctx_501_ = lean_ctor_get(v___y_489_, 2);
v_options_502_ = lean_ctor_get(v_toCold_499_, 2);
lean_inc_ref(v_options_502_);
lean_inc_ref(v_lctx_501_);
v___x_503_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_503_, 0, v_env_497_);
lean_ctor_set(v___x_503_, 1, v_mctx_500_);
lean_ctor_set(v___x_503_, 2, v_lctx_501_);
lean_ctor_set(v___x_503_, 3, v_options_502_);
v___x_504_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v_msgData_488_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(lean_object* v_msg_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_ref_519_; lean_object* v___x_520_; lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_529_; 
v_ref_519_ = lean_ctor_get(v___y_516_, 2);
v___x_520_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msg_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_529_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_527_; 
lean_inc(v_ref_519_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v_ref_519_);
lean_ctor_set(v___x_525_, 1, v_a_521_);
if (v_isShared_524_ == 0)
{
lean_ctor_set_tag(v___x_523_, 1);
lean_ctor_set(v___x_523_, 0, v___x_525_);
v___x_527_ = v___x_523_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_msg_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object* v_ref_537_, lean_object* v_msg_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_toCold_544_; lean_object* v_currRecDepth_545_; lean_object* v_ref_546_; uint16_t v_optionFlags_547_; uint8_t v_suppressElabErrors_548_; uint8_t v_isRecordingDeps_549_; lean_object* v_ref_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_toCold_544_ = lean_ctor_get(v___y_541_, 0);
v_currRecDepth_545_ = lean_ctor_get(v___y_541_, 1);
v_ref_546_ = lean_ctor_get(v___y_541_, 2);
v_optionFlags_547_ = lean_ctor_get_uint16(v___y_541_, sizeof(void*)*3);
v_suppressElabErrors_548_ = lean_ctor_get_uint8(v___y_541_, sizeof(void*)*3 + 2);
v_isRecordingDeps_549_ = lean_ctor_get_uint8(v___y_541_, sizeof(void*)*3 + 3);
v_ref_550_ = l_Lean_replaceRef(v_ref_537_, v_ref_546_);
lean_inc(v_currRecDepth_545_);
lean_inc_ref(v_toCold_544_);
v___x_551_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_551_, 0, v_toCold_544_);
lean_ctor_set(v___x_551_, 1, v_currRecDepth_545_);
lean_ctor_set(v___x_551_, 2, v_ref_550_);
lean_ctor_set_uint16(v___x_551_, sizeof(void*)*3, v_optionFlags_547_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*3 + 2, v_suppressElabErrors_548_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*3 + 3, v_isRecordingDeps_549_);
v___x_552_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_538_, v___y_539_, v___y_540_, v___x_551_, v___y_542_);
lean_dec_ref_known(v___x_551_, 3);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object* v_ref_553_, lean_object* v_msg_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_553_, v_msg_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v_ref_553_);
return v_res_560_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__1(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__0));
v___x_563_ = l_Lean_stringToMessageData(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__3(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__2));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__5(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__4));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__9(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__8));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__12(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__11));
v___x_580_ = l_Lean_MessageData_ofFormat(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object* v_funName_581_, lean_object* v_extraParams_582_, lean_object* v_tb_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
uint8_t v_synthetic_589_; 
v_synthetic_589_ = lean_ctor_get_uint8(v_tb_583_, sizeof(void*)*3 + 1);
if (v_synthetic_589_ == 0)
{
lean_object* v_ref_590_; lean_object* v_vars_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_ref_590_ = lean_ctor_get(v_tb_583_, 0);
v_vars_591_ = lean_ctor_get(v_tb_583_, 1);
v___x_592_ = lean_array_get_size(v_vars_591_);
v___x_593_ = lean_nat_dec_lt(v_extraParams_582_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v_extraParams_582_);
lean_dec(v_funName_581_);
v___x_594_ = lean_box(0);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_msg_606_; lean_object* v___x_607_; lean_object* v_ident_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_596_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_592_);
v___x_597_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__1, &l_Lean_Elab_TerminationBy_checkVars___closed__1_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__1);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_inc(v_funName_581_);
v___x_599_ = l_Lean_MessageData_ofName(v_funName_581_);
v___x_600_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__3, &l_Lean_Elab_TerminationBy_checkVars___closed__3_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__3);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_582_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__5, &l_Lean_Elab_TerminationBy_checkVars___closed__5_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__5);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v_msg_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_606_, 0, v___x_598_);
lean_ctor_set(v_msg_606_, 1, v___x_605_);
v___x_607_ = lean_unsigned_to_nat(0u);
v_ident_608_ = lean_array_fget_borrowed(v_vars_591_, v___x_607_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__7));
lean_inc(v_ident_608_);
v___x_610_ = l_Lean_Syntax_isOfKind(v_ident_608_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; 
lean_dec(v_funName_581_);
v___x_611_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_590_, v_msg_606_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
return v___x_611_;
}
else
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = l_Lean_TSyntax_getId(v_ident_608_);
v___x_613_ = l_Lean_Name_isSuffixOf(v___x_612_, v_funName_581_);
lean_dec(v_funName_581_);
lean_dec(v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_590_, v_msg_606_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_msg_618_; lean_object* v___x_619_; 
v___x_615_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__9, &l_Lean_Elab_TerminationBy_checkVars___closed__9_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__9);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v_msg_606_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__12, &l_Lean_Elab_TerminationBy_checkVars___closed__12_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__12);
v_msg_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_618_, 0, v___x_616_);
lean_ctor_set(v_msg_618_, 1, v___x_617_);
v___x_619_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_590_, v_msg_618_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
return v___x_619_;
}
}
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_extraParams_582_);
lean_dec(v_funName_581_);
v___x_620_ = lean_box(0);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object* v_funName_622_, lean_object* v_extraParams_623_, lean_object* v_tb_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_Elab_TerminationBy_checkVars(v_funName_622_, v_extraParams_623_, v_tb_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec_ref(v_tb_624_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_object* v_00_u03b1_631_, lean_object* v_ref_632_, lean_object* v_msg_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_632_, v_msg_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object* v_00_u03b1_640_, lean_object* v_ref_641_, lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(v_00_u03b1_640_, v_ref_641_, v_msg_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v_ref_641_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_object* v_00_u03b1_649_, lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_657_, lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_657_, v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object* v_val_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_666_, 0, v_val_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object* v_stx_667_, lean_object* v_terminationBy_x3f_x3f_668_, lean_object* v_terminationBy_x3f_669_, lean_object* v_partialFixpoint_x3f_670_, lean_object* v___x_671_, uint8_t v___x_672_, lean_object* v_toPure_673_, lean_object* v_decreasingBy_x3f_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_675_, 0, v_stx_667_);
lean_ctor_set(v___x_675_, 1, v_terminationBy_x3f_x3f_668_);
lean_ctor_set(v___x_675_, 2, v_terminationBy_x3f_669_);
lean_ctor_set(v___x_675_, 3, v_partialFixpoint_x3f_670_);
lean_ctor_set(v___x_675_, 4, v_decreasingBy_x3f_674_);
lean_ctor_set(v___x_675_, 5, v___x_671_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*6, v___x_672_);
v___x_676_ = lean_apply_2(v_toPure_673_, lean_box(0), v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed(lean_object* v_stx_677_, lean_object* v_terminationBy_x3f_x3f_678_, lean_object* v_terminationBy_x3f_679_, lean_object* v_partialFixpoint_x3f_680_, lean_object* v___x_681_, lean_object* v___x_682_, lean_object* v_toPure_683_, lean_object* v_decreasingBy_x3f_684_){
_start:
{
uint8_t v___x_2906__boxed_685_; lean_object* v_res_686_; 
v___x_2906__boxed_685_ = lean_unbox(v___x_682_);
v_res_686_ = l_Lean_Elab_elabTerminationHints___redArg___lam__1(v_stx_677_, v_terminationBy_x3f_x3f_678_, v_terminationBy_x3f_679_, v_partialFixpoint_x3f_680_, v___x_681_, v___x_2906__boxed_685_, v_toPure_683_, v_decreasingBy_x3f_684_);
return v_res_686_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1));
v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* v_stx_691_, lean_object* v_terminationBy_x3f_x3f_692_, lean_object* v_terminationBy_x3f_693_, lean_object* v___x_694_, uint8_t v___x_695_, lean_object* v_toPure_696_, lean_object* v_d_x3f_697_, lean_object* v_toBind_698_, lean_object* v_toFunctor_699_, lean_object* v___f_700_, lean_object* v___x_701_, lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v___x_706_, lean_object* v_partialFixpoint_x3f_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___f_709_; 
v___x_708_ = lean_box(v___x_695_);
lean_inc(v_toPure_696_);
v___f_709_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_709_, 0, v_stx_691_);
lean_closure_set(v___f_709_, 1, v_terminationBy_x3f_x3f_692_);
lean_closure_set(v___f_709_, 2, v_terminationBy_x3f_693_);
lean_closure_set(v___f_709_, 3, v_partialFixpoint_x3f_707_);
lean_closure_set(v___f_709_, 4, v___x_694_);
lean_closure_set(v___f_709_, 5, v___x_708_);
lean_closure_set(v___f_709_, 6, v_toPure_696_);
if (lean_obj_tag(v_d_x3f_697_) == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_702_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___f_700_);
lean_dec_ref(v_toFunctor_699_);
v___x_710_ = lean_box(0);
v___x_711_ = lean_apply_2(v_toPure_696_, lean_box(0), v___x_710_);
v___x_712_ = lean_apply_4(v_toBind_698_, lean_box(0), lean_box(0), v___x_711_, v___f_709_);
return v___x_712_;
}
else
{
lean_object* v_val_713_; lean_object* v_map_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_732_; 
v_val_713_ = lean_ctor_get(v_d_x3f_697_, 0);
lean_inc(v_val_713_);
lean_dec_ref_known(v_d_x3f_697_, 1);
v_map_714_ = lean_ctor_get(v_toFunctor_699_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_toFunctor_699_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v_toFunctor_699_, 1);
lean_dec(v_unused_733_);
v___x_716_ = v_toFunctor_699_;
v_isShared_717_ = v_isSharedCheck_732_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_map_714_);
lean_dec(v_toFunctor_699_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_732_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___y_719_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0));
v___x_723_ = l_Lean_Name_mkStr4(v___x_701_, v___x_702_, v___x_703_, v___x_722_);
lean_inc(v_val_713_);
v___x_724_ = l_Lean_Syntax_isOfKind(v_val_713_, v___x_723_);
lean_dec(v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_del_object(v___x_716_);
lean_dec(v_toPure_696_);
v___x_725_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2, &l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2);
v___x_726_ = l_Lean_throwErrorAt___redArg(v_inst_704_, v_inst_705_, v_val_713_, v___x_725_);
v___y_719_ = v___x_726_;
goto v___jp_718_;
}
else
{
lean_object* v_tactic_727_; lean_object* v___x_729_; 
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_704_);
v_tactic_727_ = l_Lean_Syntax_getArg(v_val_713_, v___x_706_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v_tactic_727_);
lean_ctor_set(v___x_716_, 0, v_val_713_);
v___x_729_ = v___x_716_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_val_713_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_tactic_727_);
v___x_729_ = v_reuseFailAlloc_731_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; 
v___x_730_ = lean_apply_2(v_toPure_696_, lean_box(0), v___x_729_);
v___y_719_ = v___x_730_;
goto v___jp_718_;
}
}
v___jp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_apply_4(v_map_714_, lean_box(0), lean_box(0), v___f_700_, v___y_719_);
v___x_721_ = lean_apply_4(v_toBind_698_, lean_box(0), lean_box(0), v___x_720_, v___f_709_);
return v___x_721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_stx_734_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_735_ = _args[1];
lean_object* v_terminationBy_x3f_736_ = _args[2];
lean_object* v___x_737_ = _args[3];
lean_object* v___x_738_ = _args[4];
lean_object* v_toPure_739_ = _args[5];
lean_object* v_d_x3f_740_ = _args[6];
lean_object* v_toBind_741_ = _args[7];
lean_object* v_toFunctor_742_ = _args[8];
lean_object* v___f_743_ = _args[9];
lean_object* v___x_744_ = _args[10];
lean_object* v___x_745_ = _args[11];
lean_object* v___x_746_ = _args[12];
lean_object* v_inst_747_ = _args[13];
lean_object* v_inst_748_ = _args[14];
lean_object* v___x_749_ = _args[15];
lean_object* v_partialFixpoint_x3f_750_ = _args[16];
_start:
{
uint8_t v___x_2924__boxed_751_; lean_object* v_res_752_; 
v___x_2924__boxed_751_ = lean_unbox(v___x_738_);
v_res_752_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_734_, v_terminationBy_x3f_x3f_735_, v_terminationBy_x3f_736_, v___x_737_, v___x_2924__boxed_751_, v_toPure_739_, v_d_x3f_740_, v_toBind_741_, v_toFunctor_742_, v___f_743_, v___x_744_, v___x_745_, v___x_746_, v_inst_747_, v_inst_748_, v___x_749_, v_partialFixpoint_x3f_750_);
lean_dec(v___x_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object* v___f_753_, lean_object* v_partialFixpoint_x3f_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = lean_apply_1(v___f_753_, v_partialFixpoint_x3f_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object* v_stx_759_, lean_object* v_terminationBy_x3f_x3f_760_, lean_object* v___x_761_, uint8_t v___x_762_, lean_object* v_toPure_763_, lean_object* v_d_x3f_764_, lean_object* v_toBind_765_, lean_object* v_toFunctor_766_, lean_object* v___f_767_, lean_object* v___x_768_, lean_object* v___x_769_, lean_object* v___x_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v___x_773_, lean_object* v_t_x3f_774_, lean_object* v_terminationBy_x3f_775_){
_start:
{
lean_object* v___x_776_; lean_object* v___f_777_; 
v___x_776_ = lean_box(v___x_762_);
lean_inc(v___x_773_);
lean_inc_ref(v___x_770_);
lean_inc_ref(v___x_769_);
lean_inc_ref(v___x_768_);
lean_inc(v_toBind_765_);
lean_inc(v_toPure_763_);
v___f_777_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed), 17, 16);
lean_closure_set(v___f_777_, 0, v_stx_759_);
lean_closure_set(v___f_777_, 1, v_terminationBy_x3f_x3f_760_);
lean_closure_set(v___f_777_, 2, v_terminationBy_x3f_775_);
lean_closure_set(v___f_777_, 3, v___x_761_);
lean_closure_set(v___f_777_, 4, v___x_776_);
lean_closure_set(v___f_777_, 5, v_toPure_763_);
lean_closure_set(v___f_777_, 6, v_d_x3f_764_);
lean_closure_set(v___f_777_, 7, v_toBind_765_);
lean_closure_set(v___f_777_, 8, v_toFunctor_766_);
lean_closure_set(v___f_777_, 9, v___f_767_);
lean_closure_set(v___f_777_, 10, v___x_768_);
lean_closure_set(v___f_777_, 11, v___x_769_);
lean_closure_set(v___f_777_, 12, v___x_770_);
lean_closure_set(v___f_777_, 13, v_inst_771_);
lean_closure_set(v___f_777_, 14, v_inst_772_);
lean_closure_set(v___f_777_, 15, v___x_773_);
if (lean_obj_tag(v_t_x3f_774_) == 1)
{
lean_object* v_val_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_855_; 
v_val_778_ = lean_ctor_get(v_t_x3f_774_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v_t_x3f_774_);
if (v_isSharedCheck_855_ == 0)
{
v___x_780_ = v_t_x3f_774_;
v_isShared_781_ = v_isSharedCheck_855_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_val_778_);
lean_dec(v_t_x3f_774_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_855_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_782_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_770_);
lean_inc_ref(v___x_769_);
lean_inc_ref(v___x_768_);
v___x_783_ = l_Lean_Name_mkStr4(v___x_768_, v___x_769_, v___x_770_, v___x_782_);
lean_inc(v_val_778_);
v___x_784_ = l_Lean_Syntax_isOfKind(v_val_778_, v___x_783_);
lean_dec(v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_770_);
lean_inc_ref(v___x_769_);
lean_inc_ref(v___x_768_);
v___x_786_ = l_Lean_Name_mkStr4(v___x_768_, v___x_769_, v___x_770_, v___x_785_);
lean_inc(v_val_778_);
v___x_787_ = l_Lean_Syntax_isOfKind(v_val_778_, v___x_786_);
lean_dec(v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_789_ = l_Lean_Name_mkStr4(v___x_768_, v___x_769_, v___x_770_, v___x_788_);
lean_inc(v_val_778_);
v___x_790_ = l_Lean_Syntax_isOfKind(v_val_778_, v___x_789_);
lean_dec(v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_del_object(v___x_780_);
lean_dec(v_val_778_);
lean_dec(v___x_773_);
v___f_791_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_791_, 0, v___f_777_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_792_);
v___x_794_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_793_, v___f_791_);
return v___x_794_;
}
else
{
lean_object* v___f_795_; lean_object* v_term_x3f_797_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___f_795_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_795_, 0, v___f_777_);
v___x_805_ = l_Lean_Syntax_getArg(v_val_778_, v___x_773_);
v___x_806_ = l_Lean_Syntax_isNone(v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_805_);
v___x_808_ = l_Lean_Syntax_matchesNull(v___x_805_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v___x_805_);
lean_del_object(v___x_780_);
lean_dec(v_val_778_);
lean_dec(v___x_773_);
v___x_809_ = lean_box(0);
v___x_810_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_809_);
v___x_811_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_810_, v___f_795_);
return v___x_811_;
}
else
{
lean_object* v_term_x3f_812_; lean_object* v___x_813_; 
v_term_x3f_812_ = l_Lean_Syntax_getArg(v___x_805_, v___x_773_);
lean_dec(v___x_773_);
lean_dec(v___x_805_);
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v_term_x3f_812_);
v_term_x3f_797_ = v___x_813_;
goto v___jp_796_;
}
}
else
{
lean_object* v___x_814_; 
lean_dec(v___x_805_);
lean_dec(v___x_773_);
v___x_814_ = lean_box(0);
v_term_x3f_797_ = v___x_814_;
goto v___jp_796_;
}
v___jp_796_:
{
uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_798_ = 2;
v___x_799_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_799_, 0, v_val_778_);
lean_ctor_set(v___x_799_, 1, v_term_x3f_797_);
lean_ctor_set_uint8(v___x_799_, sizeof(void*)*2, v___x_798_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_799_);
v___x_801_ = v___x_780_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_804_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_801_);
v___x_803_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_802_, v___f_795_);
return v___x_803_;
}
}
}
}
else
{
lean_object* v___f_815_; lean_object* v_term_x3f_817_; lean_object* v___x_825_; uint8_t v___x_826_; 
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_769_);
lean_dec_ref(v___x_768_);
v___f_815_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_815_, 0, v___f_777_);
v___x_825_ = l_Lean_Syntax_getArg(v_val_778_, v___x_773_);
v___x_826_ = l_Lean_Syntax_isNone(v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_825_);
v___x_828_ = l_Lean_Syntax_matchesNull(v___x_825_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec(v___x_825_);
lean_del_object(v___x_780_);
lean_dec(v_val_778_);
lean_dec(v___x_773_);
v___x_829_ = lean_box(0);
v___x_830_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_829_);
v___x_831_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_830_, v___f_815_);
return v___x_831_;
}
else
{
lean_object* v_term_x3f_832_; lean_object* v___x_833_; 
v_term_x3f_832_ = l_Lean_Syntax_getArg(v___x_825_, v___x_773_);
lean_dec(v___x_773_);
lean_dec(v___x_825_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v_term_x3f_832_);
v_term_x3f_817_ = v___x_833_;
goto v___jp_816_;
}
}
else
{
lean_object* v___x_834_; 
lean_dec(v___x_825_);
lean_dec(v___x_773_);
v___x_834_ = lean_box(0);
v_term_x3f_817_ = v___x_834_;
goto v___jp_816_;
}
v___jp_816_:
{
uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_818_ = 1;
v___x_819_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_819_, 0, v_val_778_);
lean_ctor_set(v___x_819_, 1, v_term_x3f_817_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*2, v___x_818_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_819_);
v___x_821_ = v___x_780_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_824_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_821_);
v___x_823_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_822_, v___f_815_);
return v___x_823_;
}
}
}
}
else
{
lean_object* v___f_835_; lean_object* v_term_x3f_837_; lean_object* v___x_845_; uint8_t v___x_846_; 
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_769_);
lean_dec_ref(v___x_768_);
v___f_835_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_835_, 0, v___f_777_);
v___x_845_ = l_Lean_Syntax_getArg(v_val_778_, v___x_773_);
v___x_846_ = l_Lean_Syntax_isNone(v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_845_);
v___x_848_ = l_Lean_Syntax_matchesNull(v___x_845_, v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec(v___x_845_);
lean_del_object(v___x_780_);
lean_dec(v_val_778_);
lean_dec(v___x_773_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_849_);
v___x_851_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_850_, v___f_835_);
return v___x_851_;
}
else
{
lean_object* v_term_x3f_852_; lean_object* v___x_853_; 
v_term_x3f_852_ = l_Lean_Syntax_getArg(v___x_845_, v___x_773_);
lean_dec(v___x_773_);
lean_dec(v___x_845_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v_term_x3f_852_);
v_term_x3f_837_ = v___x_853_;
goto v___jp_836_;
}
}
else
{
lean_object* v___x_854_; 
lean_dec(v___x_845_);
lean_dec(v___x_773_);
v___x_854_ = lean_box(0);
v_term_x3f_837_ = v___x_854_;
goto v___jp_836_;
}
v___jp_836_:
{
uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_838_ = 0;
v___x_839_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_839_, 0, v_val_778_);
lean_ctor_set(v___x_839_, 1, v_term_x3f_837_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*2, v___x_838_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_839_);
v___x_841_ = v___x_780_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_844_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_841_);
v___x_843_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_842_, v___f_835_);
return v___x_843_;
}
}
}
}
}
else
{
lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v_t_x3f_774_);
lean_dec(v___x_773_);
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_769_);
lean_dec_ref(v___x_768_);
v___f_856_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_856_, 0, v___f_777_);
v___x_857_ = lean_box(0);
v___x_858_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_857_);
v___x_859_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_858_, v___f_856_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_stx_860_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_861_ = _args[1];
lean_object* v___x_862_ = _args[2];
lean_object* v___x_863_ = _args[3];
lean_object* v_toPure_864_ = _args[4];
lean_object* v_d_x3f_865_ = _args[5];
lean_object* v_toBind_866_ = _args[6];
lean_object* v_toFunctor_867_ = _args[7];
lean_object* v___f_868_ = _args[8];
lean_object* v___x_869_ = _args[9];
lean_object* v___x_870_ = _args[10];
lean_object* v___x_871_ = _args[11];
lean_object* v_inst_872_ = _args[12];
lean_object* v_inst_873_ = _args[13];
lean_object* v___x_874_ = _args[14];
lean_object* v_t_x3f_875_ = _args[15];
lean_object* v_terminationBy_x3f_876_ = _args[16];
_start:
{
uint8_t v___x_3013__boxed_877_; lean_object* v_res_878_; 
v___x_3013__boxed_877_ = lean_unbox(v___x_863_);
v_res_878_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11(v_stx_860_, v_terminationBy_x3f_x3f_861_, v___x_862_, v___x_3013__boxed_877_, v_toPure_864_, v_d_x3f_865_, v_toBind_866_, v_toFunctor_867_, v___f_868_, v___x_869_, v___x_870_, v___x_871_, v_inst_872_, v_inst_873_, v___x_874_, v_t_x3f_875_, v_terminationBy_x3f_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* v___f_879_, lean_object* v_terminationBy_x3f_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = lean_apply_1(v___f_879_, v_terminationBy_x3f_880_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2));
v___x_886_ = l_Lean_stringToMessageData(v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* v_stx_890_, lean_object* v___x_891_, uint8_t v___x_892_, lean_object* v_toPure_893_, lean_object* v_d_x3f_894_, lean_object* v_toBind_895_, lean_object* v_toFunctor_896_, lean_object* v___f_897_, lean_object* v___x_898_, lean_object* v___x_899_, lean_object* v___x_900_, lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v___x_903_, lean_object* v_t_x3f_904_, lean_object* v_terminationBy_x3f_x3f_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___f_907_; 
v___x_906_ = lean_box(v___x_892_);
lean_inc(v_t_x3f_904_);
lean_inc(v___x_903_);
lean_inc_ref(v_inst_902_);
lean_inc_ref(v_inst_901_);
lean_inc_ref(v___x_900_);
lean_inc_ref(v___x_899_);
lean_inc_ref(v___x_898_);
lean_inc(v_toBind_895_);
lean_inc(v_toPure_893_);
lean_inc(v___x_891_);
v___f_907_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_907_, 0, v_stx_890_);
lean_closure_set(v___f_907_, 1, v_terminationBy_x3f_x3f_905_);
lean_closure_set(v___f_907_, 2, v___x_891_);
lean_closure_set(v___f_907_, 3, v___x_906_);
lean_closure_set(v___f_907_, 4, v_toPure_893_);
lean_closure_set(v___f_907_, 5, v_d_x3f_894_);
lean_closure_set(v___f_907_, 6, v_toBind_895_);
lean_closure_set(v___f_907_, 7, v_toFunctor_896_);
lean_closure_set(v___f_907_, 8, v___f_897_);
lean_closure_set(v___f_907_, 9, v___x_898_);
lean_closure_set(v___f_907_, 10, v___x_899_);
lean_closure_set(v___f_907_, 11, v___x_900_);
lean_closure_set(v___f_907_, 12, v_inst_901_);
lean_closure_set(v___f_907_, 13, v_inst_902_);
lean_closure_set(v___f_907_, 14, v___x_903_);
lean_closure_set(v___f_907_, 15, v_t_x3f_904_);
if (lean_obj_tag(v_t_x3f_904_) == 1)
{
lean_object* v_val_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_1020_; 
v_val_908_ = lean_ctor_get(v_t_x3f_904_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_t_x3f_904_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_910_ = v_t_x3f_904_;
v_isShared_911_ = v_isSharedCheck_1020_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_val_908_);
lean_dec(v_t_x3f_904_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_1020_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_912_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0));
lean_inc_ref(v___x_900_);
lean_inc_ref(v___x_899_);
lean_inc_ref(v___x_898_);
v___x_913_ = l_Lean_Name_mkStr4(v___x_898_, v___x_899_, v___x_900_, v___x_912_);
lean_inc(v_val_908_);
v___x_914_ = l_Lean_Syntax_isOfKind(v_val_908_, v___x_913_);
lean_dec(v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
lean_del_object(v___x_910_);
lean_dec(v___x_891_);
v___x_915_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1));
lean_inc_ref(v___x_900_);
lean_inc_ref(v___x_899_);
lean_inc_ref(v___x_898_);
v___x_916_ = l_Lean_Name_mkStr4(v___x_898_, v___x_899_, v___x_900_, v___x_915_);
lean_inc(v_val_908_);
v___x_917_ = l_Lean_Syntax_isOfKind(v_val_908_, v___x_916_);
lean_dec(v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_918_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_900_);
lean_inc_ref(v___x_899_);
lean_inc_ref(v___x_898_);
v___x_919_ = l_Lean_Name_mkStr4(v___x_898_, v___x_899_, v___x_900_, v___x_918_);
lean_inc(v_val_908_);
v___x_920_ = l_Lean_Syntax_isOfKind(v_val_908_, v___x_919_);
lean_dec(v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_900_);
lean_inc_ref(v___x_899_);
lean_inc_ref(v___x_898_);
v___x_922_ = l_Lean_Name_mkStr4(v___x_898_, v___x_899_, v___x_900_, v___x_921_);
lean_inc(v_val_908_);
v___x_923_ = l_Lean_Syntax_isOfKind(v_val_908_, v___x_922_);
lean_dec(v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_924_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_925_ = l_Lean_Name_mkStr4(v___x_898_, v___x_899_, v___x_900_, v___x_924_);
lean_inc(v_val_908_);
v___x_926_ = l_Lean_Syntax_isOfKind(v_val_908_, v___x_925_);
lean_dec(v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec(v___x_903_);
lean_dec(v_toPure_893_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_927_, 0, v___f_907_);
v___x_928_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_929_ = l_Lean_throwErrorAt___redArg(v_inst_901_, v_inst_902_, v_val_908_, v___x_928_);
v___x_930_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_929_, v___f_927_);
return v___x_930_;
}
else
{
lean_object* v___f_931_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_931_, 0, v___f_907_);
v___x_936_ = l_Lean_Syntax_getArg(v_val_908_, v___x_903_);
lean_dec(v___x_903_);
v___x_937_ = l_Lean_Syntax_isNone(v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = lean_unsigned_to_nat(2u);
v___x_939_ = l_Lean_Syntax_matchesNull(v___x_936_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v_toPure_893_);
v___x_940_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_941_ = l_Lean_throwErrorAt___redArg(v_inst_901_, v_inst_902_, v_val_908_, v___x_940_);
v___x_942_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_941_, v___f_931_);
return v___x_942_;
}
else
{
lean_dec(v_val_908_);
lean_dec_ref(v_inst_902_);
lean_dec_ref(v_inst_901_);
goto v___jp_932_;
}
}
else
{
lean_dec(v___x_936_);
lean_dec(v_val_908_);
lean_dec_ref(v_inst_902_);
lean_dec_ref(v_inst_901_);
goto v___jp_932_;
}
v___jp_932_:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_box(0);
v___x_934_ = lean_apply_2(v_toPure_893_, lean_box(0), v___x_933_);
v___x_935_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_934_, v___f_931_);
return v___x_935_;
}
}
}
else
{
lean_object* v___f_943_; lean_object* v___x_948_; uint8_t v___x_949_; 
lean_dec_ref(v___x_900_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v___x_898_);
v___f_943_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_943_, 0, v___f_907_);
v___x_948_ = l_Lean_Syntax_getArg(v_val_908_, v___x_903_);
lean_dec(v___x_903_);
v___x_949_ = l_Lean_Syntax_isNone(v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_950_ = lean_unsigned_to_nat(2u);
v___x_951_ = l_Lean_Syntax_matchesNull(v___x_948_, v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec(v_toPure_893_);
v___x_952_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_953_ = l_Lean_throwErrorAt___redArg(v_inst_901_, v_inst_902_, v_val_908_, v___x_952_);
v___x_954_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_953_, v___f_943_);
return v___x_954_;
}
else
{
lean_dec(v_val_908_);
lean_dec_ref(v_inst_902_);
lean_dec_ref(v_inst_901_);
goto v___jp_944_;
}
}
else
{
lean_dec(v___x_948_);
lean_dec(v_val_908_);
lean_dec_ref(v_inst_902_);
lean_dec_ref(v_inst_901_);
goto v___jp_944_;
}
v___jp_944_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = lean_box(0);
v___x_946_ = lean_apply_2(v_toPure_893_, lean_box(0), v___x_945_);
v___x_947_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_946_, v___f_943_);
return v___x_947_;
}
}
}
else
{
lean_object* v___f_955_; lean_object* v___x_960_; uint8_t v___x_961_; 
lean_dec_ref(v___x_900_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v___x_898_);
v___f_955_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_955_, 0, v___f_907_);
v___x_960_ = l_Lean_Syntax_getArg(v_val_908_, v___x_903_);
lean_dec(v___x_903_);
v___x_961_ = l_Lean_Syntax_isNone(v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_962_ = lean_unsigned_to_nat(2u);
v___x_963_ = l_Lean_Syntax_matchesNull(v___x_960_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v_toPure_893_);
v___x_964_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_965_ = l_Lean_throwErrorAt___redArg(v_inst_901_, v_inst_902_, v_val_908_, v___x_964_);
v___x_966_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_965_, v___f_955_);
return v___x_966_;
}
else
{
lean_dec(v_val_908_);
lean_dec_ref(v_inst_902_);
lean_dec_ref(v_inst_901_);
goto v___jp_956_;
}
}
else
{
lean_dec(v___x_960_);
lean_dec(v_val_908_);
lean_dec_ref(v_inst_902_);
lean_dec_ref(v_inst_901_);
goto v___jp_956_;
}
v___jp_956_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = lean_box(0);
v___x_958_ = lean_apply_2(v_toPure_893_, lean_box(0), v___x_957_);
v___x_959_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_958_, v___f_955_);
return v___x_959_;
}
}
}
else
{
lean_object* v___f_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec(v_val_908_);
lean_dec(v___x_903_);
lean_dec_ref(v_inst_902_);
lean_dec_ref(v_inst_901_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v___x_898_);
v___f_967_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_967_, 0, v___f_907_);
v___x_968_ = lean_box(0);
v___x_969_ = lean_apply_2(v_toPure_893_, lean_box(0), v___x_968_);
v___x_970_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_969_, v___f_967_);
return v___x_970_;
}
}
else
{
lean_object* v___f_971_; lean_object* v___y_973_; lean_object* v___y_974_; uint8_t v___y_975_; uint8_t v___y_976_; lean_object* v___y_984_; uint8_t v___y_985_; uint8_t v___y_986_; lean_object* v_s_993_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
lean_dec_ref(v___x_900_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v___x_898_);
v___f_971_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_971_, 0, v___f_907_);
v___x_1011_ = l_Lean_Syntax_getArg(v_val_908_, v___x_903_);
v___x_1012_ = l_Lean_Syntax_isNone(v___x_1011_);
if (v___x_1012_ == 0)
{
uint8_t v___x_1013_; 
lean_inc(v___x_1011_);
v___x_1013_ = l_Lean_Syntax_matchesNull(v___x_1011_, v___x_903_);
lean_dec(v___x_903_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec(v___x_1011_);
lean_del_object(v___x_910_);
lean_dec(v_toPure_893_);
lean_dec(v___x_891_);
v___x_1014_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1015_ = l_Lean_throwErrorAt___redArg(v_inst_901_, v_inst_902_, v_val_908_, v___x_1014_);
v___x_1016_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_1015_, v___f_971_);
return v___x_1016_;
}
else
{
lean_object* v_s_1017_; lean_object* v___x_1018_; 
v_s_1017_ = l_Lean_Syntax_getArg(v___x_1011_, v___x_891_);
lean_dec(v___x_1011_);
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_s_1017_);
v_s_993_ = v___x_1018_;
goto v___jp_992_;
}
}
else
{
lean_object* v___x_1019_; 
lean_dec(v___x_1011_);
lean_dec(v___x_903_);
v___x_1019_ = lean_box(0);
v_s_993_ = v___x_1019_;
goto v___jp_992_;
}
v___jp_972_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_977_, 0, v_val_908_);
lean_ctor_set(v___x_977_, 1, v___y_974_);
lean_ctor_set(v___x_977_, 2, v___y_973_);
lean_ctor_set_uint8(v___x_977_, sizeof(void*)*3, v___y_976_);
lean_ctor_set_uint8(v___x_977_, sizeof(void*)*3 + 1, v___y_975_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_977_);
v___x_979_ = v___x_910_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_982_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_apply_2(v_toPure_893_, lean_box(0), v___x_979_);
v___x_981_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_980_, v___f_971_);
return v___x_981_;
}
}
v___jp_983_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_987_ = lean_mk_empty_array_with_capacity(v___x_891_);
lean_dec(v___x_891_);
v___x_988_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_988_, 0, v_val_908_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
lean_ctor_set(v___x_988_, 2, v___y_984_);
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*3, v___y_986_);
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*3 + 1, v___y_985_);
v___x_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
v___x_990_ = lean_apply_2(v_toPure_893_, lean_box(0), v___x_989_);
v___x_991_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_990_, v___f_971_);
return v___x_991_;
}
v___jp_992_:
{
lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_994_ = lean_unsigned_to_nat(2u);
v___x_995_ = l_Lean_Syntax_getArg(v_val_908_, v___x_994_);
lean_inc(v___x_995_);
v___x_996_ = l_Lean_Syntax_matchesNull(v___x_995_, v___x_994_);
if (v___x_996_ == 0)
{
uint8_t v___x_997_; 
lean_del_object(v___x_910_);
v___x_997_ = l_Lean_Syntax_matchesNull(v___x_995_, v___x_891_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec(v_s_993_);
lean_dec(v_toPure_893_);
lean_dec(v___x_891_);
v___x_998_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_999_ = l_Lean_throwErrorAt___redArg(v_inst_901_, v_inst_902_, v_val_908_, v___x_998_);
v___x_1000_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_999_, v___f_971_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; lean_object* v_body_1002_; 
lean_dec_ref(v_inst_902_);
lean_dec_ref(v_inst_901_);
v___x_1001_ = lean_unsigned_to_nat(3u);
v_body_1002_ = l_Lean_Syntax_getArg(v_val_908_, v___x_1001_);
if (lean_obj_tag(v_s_993_) == 0)
{
v___y_984_ = v_body_1002_;
v___y_985_ = v___x_996_;
v___y_986_ = v___x_996_;
goto v___jp_983_;
}
else
{
lean_dec_ref_known(v_s_993_, 1);
v___y_984_ = v_body_1002_;
v___y_985_ = v___x_996_;
v___y_986_ = v___x_997_;
goto v___jp_983_;
}
}
}
else
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = l_Lean_Syntax_getArg(v___x_995_, v___x_891_);
lean_dec(v___x_995_);
lean_inc(v___x_1003_);
v___x_1004_ = l_Lean_Syntax_matchesNull(v___x_1003_, v___x_891_);
lean_dec(v___x_891_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v_body_1006_; lean_object* v_vars_1007_; 
lean_dec_ref(v_inst_902_);
lean_dec_ref(v_inst_901_);
v___x_1005_ = lean_unsigned_to_nat(3u);
v_body_1006_ = l_Lean_Syntax_getArg(v_val_908_, v___x_1005_);
v_vars_1007_ = l_Lean_Syntax_getArgs(v___x_1003_);
lean_dec(v___x_1003_);
if (lean_obj_tag(v_s_993_) == 0)
{
v___y_973_ = v_body_1006_;
v___y_974_ = v_vars_1007_;
v___y_975_ = v___x_1004_;
v___y_976_ = v___x_1004_;
goto v___jp_972_;
}
else
{
lean_dec_ref_known(v_s_993_, 1);
v___y_973_ = v_body_1006_;
v___y_974_ = v_vars_1007_;
v___y_975_ = v___x_1004_;
v___y_976_ = v___x_996_;
goto v___jp_972_;
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_dec(v___x_1003_);
lean_dec(v_s_993_);
lean_del_object(v___x_910_);
lean_dec(v_toPure_893_);
v___x_1008_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
v___x_1009_ = l_Lean_throwErrorAt___redArg(v_inst_901_, v_inst_902_, v_val_908_, v___x_1008_);
v___x_1010_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_1009_, v___f_971_);
return v___x_1010_;
}
}
}
}
}
}
else
{
lean_object* v___f_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec(v_t_x3f_904_);
lean_dec(v___x_903_);
lean_dec_ref(v_inst_902_);
lean_dec_ref(v_inst_901_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v___x_898_);
lean_dec(v___x_891_);
v___f_1021_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1021_, 0, v___f_907_);
v___x_1022_ = lean_box(0);
v___x_1023_ = lean_apply_2(v_toPure_893_, lean_box(0), v___x_1022_);
v___x_1024_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_1023_, v___f_1021_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed(lean_object* v_stx_1025_, lean_object* v___x_1026_, lean_object* v___x_1027_, lean_object* v_toPure_1028_, lean_object* v_d_x3f_1029_, lean_object* v_toBind_1030_, lean_object* v_toFunctor_1031_, lean_object* v___f_1032_, lean_object* v___x_1033_, lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v___x_1038_, lean_object* v_t_x3f_1039_, lean_object* v_terminationBy_x3f_x3f_1040_){
_start:
{
uint8_t v___x_3237__boxed_1041_; lean_object* v_res_1042_; 
v___x_3237__boxed_1041_ = lean_unbox(v___x_1027_);
v_res_1042_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19(v_stx_1025_, v___x_1026_, v___x_3237__boxed_1041_, v_toPure_1028_, v_d_x3f_1029_, v_toBind_1030_, v_toFunctor_1031_, v___f_1032_, v___x_1033_, v___x_1034_, v___x_1035_, v_inst_1036_, v_inst_1037_, v___x_1038_, v_t_x3f_1039_, v_terminationBy_x3f_x3f_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* v___f_1043_, lean_object* v_terminationBy_x3f_x3f_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_apply_1(v___f_1043_, v_terminationBy_x3f_x3f_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_stx_1070_){
_start:
{
if (lean_obj_tag(v_stx_1070_) == 0)
{
lean_object* v_toApplicative_1071_; lean_object* v_toPure_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_toApplicative_1071_ = lean_ctor_get(v_inst_1068_, 0);
lean_inc_ref(v_toApplicative_1071_);
lean_dec_ref(v_inst_1069_);
lean_dec_ref(v_inst_1068_);
v_toPure_1072_ = lean_ctor_get(v_toApplicative_1071_, 1);
lean_inc(v_toPure_1072_);
lean_dec_ref(v_toApplicative_1071_);
v___x_1073_ = 1;
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1076_, 0, v_stx_1070_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
lean_ctor_set(v___x_1076_, 2, v___x_1075_);
lean_ctor_set(v___x_1076_, 3, v___x_1075_);
lean_ctor_set(v___x_1076_, 4, v___x_1075_);
lean_ctor_set(v___x_1076_, 5, v___x_1074_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*6, v___x_1073_);
v___x_1077_ = lean_apply_2(v_toPure_1072_, lean_box(0), v___x_1076_);
return v___x_1077_;
}
else
{
lean_object* v_toApplicative_1078_; lean_object* v_toBind_1079_; lean_object* v_toFunctor_1080_; lean_object* v_toPure_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_toApplicative_1078_ = lean_ctor_get(v_inst_1068_, 0);
v_toBind_1079_ = lean_ctor_get(v_inst_1068_, 1);
v_toFunctor_1080_ = lean_ctor_get(v_toApplicative_1078_, 0);
v_toPure_1081_ = lean_ctor_get(v_toApplicative_1078_, 1);
v___x_1082_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__0));
v___x_1083_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__1));
v___x_1084_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__2));
v___x_1085_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__4));
lean_inc(v_stx_1070_);
v___x_1086_ = l_Lean_Syntax_isOfKind(v_stx_1070_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1087_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1088_ = lean_box(0);
lean_inc_n(v_stx_1070_, 2);
v___x_1089_ = l_Lean_Syntax_formatStx(v_stx_1070_, v___x_1088_, v___x_1086_);
v___x_1090_ = l_Std_Format_defWidth;
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = l_Std_Format_pretty(v___x_1089_, v___x_1090_, v___x_1091_, v___x_1091_);
v___x_1093_ = lean_string_append(v___x_1087_, v___x_1092_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1095_ = lean_string_append(v___x_1093_, v___x_1094_);
v___x_1096_ = l_Lean_Syntax_getKind(v_stx_1070_);
v___x_1097_ = 1;
v___x_1098_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1096_, v___x_1097_);
v___x_1099_ = lean_string_append(v___x_1095_, v___x_1098_);
lean_dec_ref(v___x_1098_);
v___x_1100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
v___x_1101_ = l_Lean_MessageData_ofFormat(v___x_1100_);
v___x_1102_ = l_Lean_throwErrorAt___redArg(v_inst_1068_, v_inst_1069_, v_stx_1070_, v___x_1101_);
return v___x_1102_;
}
else
{
lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v_d_x3f_1108_; lean_object* v_t_x3f_1133_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___f_1103_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__7));
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1171_ = l_Lean_Syntax_getArg(v_stx_1070_, v___x_1104_);
v___x_1172_ = l_Lean_Syntax_isNone(v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1171_);
v___x_1174_ = l_Lean_Syntax_matchesNull(v___x_1171_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v___x_1171_);
v___x_1175_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1176_ = lean_box(0);
lean_inc_n(v_stx_1070_, 2);
v___x_1177_ = l_Lean_Syntax_formatStx(v_stx_1070_, v___x_1176_, v___x_1174_);
v___x_1178_ = l_Std_Format_defWidth;
v___x_1179_ = l_Std_Format_pretty(v___x_1177_, v___x_1178_, v___x_1104_, v___x_1104_);
v___x_1180_ = lean_string_append(v___x_1175_, v___x_1179_);
lean_dec_ref(v___x_1179_);
v___x_1181_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1182_ = lean_string_append(v___x_1180_, v___x_1181_);
v___x_1183_ = l_Lean_Syntax_getKind(v_stx_1070_);
v___x_1184_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1183_, v___x_1086_);
v___x_1185_ = lean_string_append(v___x_1182_, v___x_1184_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
v___x_1187_ = l_Lean_MessageData_ofFormat(v___x_1186_);
v___x_1188_ = l_Lean_throwErrorAt___redArg(v_inst_1068_, v_inst_1069_, v_stx_1070_, v___x_1187_);
return v___x_1188_;
}
else
{
lean_object* v_t_x3f_1189_; lean_object* v___x_1190_; 
v_t_x3f_1189_ = l_Lean_Syntax_getArg(v___x_1171_, v___x_1104_);
lean_dec(v___x_1171_);
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_t_x3f_1189_);
v_t_x3f_1133_ = v___x_1190_;
goto v___jp_1132_;
}
}
else
{
lean_object* v___x_1191_; 
lean_dec(v___x_1171_);
v___x_1191_ = lean_box(0);
v_t_x3f_1133_ = v___x_1191_;
goto v___jp_1132_;
}
v___jp_1105_:
{
lean_object* v___x_1109_; lean_object* v___f_1110_; 
v___x_1109_ = lean_box(v___x_1086_);
lean_inc(v___y_1106_);
lean_inc(v_toBind_1079_);
lean_inc(v_toPure_1081_);
v___f_1110_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed), 16, 15);
lean_closure_set(v___f_1110_, 0, v_stx_1070_);
lean_closure_set(v___f_1110_, 1, v___x_1104_);
lean_closure_set(v___f_1110_, 2, v___x_1109_);
lean_closure_set(v___f_1110_, 3, v_toPure_1081_);
lean_closure_set(v___f_1110_, 4, v_d_x3f_1108_);
lean_closure_set(v___f_1110_, 5, v_toBind_1079_);
lean_closure_set(v___f_1110_, 6, v_toFunctor_1080_);
lean_closure_set(v___f_1110_, 7, v___f_1103_);
lean_closure_set(v___f_1110_, 8, v___x_1082_);
lean_closure_set(v___f_1110_, 9, v___x_1083_);
lean_closure_set(v___f_1110_, 10, v___x_1084_);
lean_closure_set(v___f_1110_, 11, v_inst_1068_);
lean_closure_set(v___f_1110_, 12, v_inst_1069_);
lean_closure_set(v___f_1110_, 13, v___y_1107_);
lean_closure_set(v___f_1110_, 14, v___y_1106_);
if (lean_obj_tag(v___y_1106_) == 1)
{
lean_object* v_val_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1127_; 
v_val_1111_ = lean_ctor_get(v___y_1106_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___y_1106_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1113_ = v___y_1106_;
v_isShared_1114_ = v_isSharedCheck_1127_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_val_1111_);
lean_dec(v___y_1106_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1127_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__8));
lean_inc(v_val_1111_);
v___x_1116_ = l_Lean_Syntax_isOfKind(v_val_1111_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___f_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_del_object(v___x_1113_);
lean_dec(v_val_1111_);
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1117_, 0, v___f_1110_);
v___x_1118_ = lean_box(0);
v___x_1119_ = lean_apply_2(v_toPure_1081_, lean_box(0), v___x_1118_);
v___x_1120_ = lean_apply_4(v_toBind_1079_, lean_box(0), lean_box(0), v___x_1119_, v___f_1117_);
return v___x_1120_;
}
else
{
lean_object* v___f_1121_; lean_object* v___x_1123_; 
v___f_1121_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1121_, 0, v___f_1110_);
if (v_isShared_1114_ == 0)
{
v___x_1123_ = v___x_1113_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_val_1111_);
v___x_1123_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_apply_2(v_toPure_1081_, lean_box(0), v___x_1123_);
v___x_1125_ = lean_apply_4(v_toBind_1079_, lean_box(0), lean_box(0), v___x_1124_, v___f_1121_);
return v___x_1125_;
}
}
}
}
else
{
lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v___y_1106_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1128_, 0, v___f_1110_);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_apply_2(v_toPure_1081_, lean_box(0), v___x_1129_);
v___x_1131_ = lean_apply_4(v_toBind_1079_, lean_box(0), lean_box(0), v___x_1130_, v___f_1128_);
return v___x_1131_;
}
}
v___jp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = lean_unsigned_to_nat(1u);
v___x_1135_ = l_Lean_Syntax_getArg(v_stx_1070_, v___x_1134_);
v___x_1136_ = l_Lean_Syntax_isNone(v___x_1135_);
if (v___x_1136_ == 0)
{
uint8_t v___x_1137_; 
lean_inc(v___x_1135_);
v___x_1137_ = l_Lean_Syntax_matchesNull(v___x_1135_, v___x_1134_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec(v___x_1135_);
lean_dec(v_t_x3f_1133_);
v___x_1138_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1139_ = lean_box(0);
lean_inc_n(v_stx_1070_, 2);
v___x_1140_ = l_Lean_Syntax_formatStx(v_stx_1070_, v___x_1139_, v___x_1137_);
v___x_1141_ = l_Std_Format_defWidth;
v___x_1142_ = l_Std_Format_pretty(v___x_1140_, v___x_1141_, v___x_1104_, v___x_1104_);
v___x_1143_ = lean_string_append(v___x_1138_, v___x_1142_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1145_ = lean_string_append(v___x_1143_, v___x_1144_);
v___x_1146_ = l_Lean_Syntax_getKind(v_stx_1070_);
v___x_1147_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1146_, v___x_1086_);
v___x_1148_ = lean_string_append(v___x_1145_, v___x_1147_);
lean_dec_ref(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
v___x_1150_ = l_Lean_MessageData_ofFormat(v___x_1149_);
v___x_1151_ = l_Lean_throwErrorAt___redArg(v_inst_1068_, v_inst_1069_, v_stx_1070_, v___x_1150_);
return v___x_1151_;
}
else
{
lean_object* v_d_x3f_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_d_x3f_1152_ = l_Lean_Syntax_getArg(v___x_1135_, v___x_1104_);
lean_dec(v___x_1135_);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__9));
lean_inc(v_d_x3f_1152_);
v___x_1154_ = l_Lean_Syntax_isOfKind(v_d_x3f_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_d_x3f_1152_);
lean_dec(v_t_x3f_1133_);
v___x_1155_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1156_ = lean_box(0);
lean_inc_n(v_stx_1070_, 2);
v___x_1157_ = l_Lean_Syntax_formatStx(v_stx_1070_, v___x_1156_, v___x_1136_);
v___x_1158_ = l_Std_Format_defWidth;
v___x_1159_ = l_Std_Format_pretty(v___x_1157_, v___x_1158_, v___x_1104_, v___x_1104_);
v___x_1160_ = lean_string_append(v___x_1155_, v___x_1159_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1162_ = lean_string_append(v___x_1160_, v___x_1161_);
v___x_1163_ = l_Lean_Syntax_getKind(v_stx_1070_);
v___x_1164_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1163_, v___x_1137_);
v___x_1165_ = lean_string_append(v___x_1162_, v___x_1164_);
lean_dec_ref(v___x_1164_);
v___x_1166_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
v___x_1167_ = l_Lean_MessageData_ofFormat(v___x_1166_);
v___x_1168_ = l_Lean_throwErrorAt___redArg(v_inst_1068_, v_inst_1069_, v_stx_1070_, v___x_1167_);
return v___x_1168_;
}
else
{
lean_object* v___x_1169_; 
lean_inc(v_toPure_1081_);
lean_inc_ref(v_toFunctor_1080_);
lean_inc(v_toBind_1079_);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_d_x3f_1152_);
v___y_1106_ = v_t_x3f_1133_;
v___y_1107_ = v___x_1134_;
v_d_x3f_1108_ = v___x_1169_;
goto v___jp_1105_;
}
}
}
else
{
lean_object* v___x_1170_; 
lean_inc(v_toPure_1081_);
lean_inc_ref(v_toFunctor_1080_);
lean_inc(v_toBind_1079_);
lean_dec(v___x_1135_);
v___x_1170_ = lean_box(0);
v___y_1106_ = v_t_x3f_1133_;
v___y_1107_ = v___x_1134_;
v_d_x3f_1108_ = v___x_1170_;
goto v___jp_1105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* v_m_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_stx_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Elab_elabTerminationHints___redArg(v_inst_1193_, v_inst_1194_, v_stx_1195_);
return v___x_1196_;
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
