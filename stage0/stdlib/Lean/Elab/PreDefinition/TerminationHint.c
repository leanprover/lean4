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
uint8_t v___y_224_; uint8_t v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v_toCold_231_; lean_object* v___y_232_; lean_object* v___y_261_; lean_object* v___y_262_; uint8_t v___y_263_; lean_object* v___y_264_; uint8_t v___y_265_; uint8_t v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_288_; lean_object* v___y_289_; uint8_t v___y_290_; uint8_t v___y_291_; uint8_t v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; uint8_t v___y_298_; uint8_t v___y_299_; uint8_t v___x_309_; uint8_t v___y_311_; uint8_t v___x_317_; 
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
lean_ctor_set(v___x_236_, 1, v___y_229_);
lean_inc_ref(v___y_228_);
lean_inc_ref(v___y_230_);
v___x_237_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_237_, 0, v___y_230_);
lean_ctor_set(v___x_237_, 1, v___y_227_);
lean_ctor_set(v___x_237_, 2, v___y_226_);
lean_ctor_set(v___x_237_, 3, v___y_228_);
lean_ctor_set(v___x_237_, 4, v___x_236_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*5, v___y_224_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*5 + 1, v___y_225_);
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
v_fileName_269_ = lean_ctor_get(v___y_264_, 0);
v_fileMap_270_ = lean_ctor_get(v___y_264_, 1);
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
v___x_277_ = l_Lean_FileMap_toPosition(v_fileMap_270_, v___y_267_);
lean_dec(v___y_267_);
v___x_278_ = l_Lean_FileMap_toPosition(v_fileMap_270_, v___y_268_);
lean_dec(v___y_268_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
v___x_280_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0));
if (v___y_266_ == 0)
{
lean_del_object(v___x_275_);
lean_dec_ref(v___y_262_);
v___y_224_ = v___y_263_;
v___y_225_ = v___y_265_;
v___y_226_ = v___x_279_;
v___y_227_ = v___x_277_;
v___y_228_ = v___x_280_;
v___y_229_ = v_a_273_;
v___y_230_ = v_fileName_269_;
v_toCold_231_ = v___y_261_;
v___y_232_ = v___y_221_;
goto v___jp_223_;
}
else
{
uint8_t v___x_281_; 
lean_inc(v_a_273_);
v___x_281_ = l_Lean_MessageData_hasTag(v___y_262_, v_a_273_);
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
v___y_224_ = v___y_263_;
v___y_225_ = v___y_265_;
v___y_226_ = v___x_279_;
v___y_227_ = v___x_277_;
v___y_228_ = v___x_280_;
v___y_229_ = v_a_273_;
v___y_230_ = v_fileName_269_;
v_toCold_231_ = v___y_261_;
v___y_232_ = v___y_221_;
goto v___jp_223_;
}
}
}
}
v___jp_287_:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Syntax_getTailPos_x3f(v___y_293_, v___y_291_);
lean_dec(v___y_293_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_inc(v___y_294_);
v___y_261_ = v___y_288_;
v___y_262_ = v___y_289_;
v___y_263_ = v___y_291_;
v___y_264_ = v___y_288_;
v___y_265_ = v___y_292_;
v___y_266_ = v___y_290_;
v___y_267_ = v___y_294_;
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
v___y_262_ = v___y_289_;
v___y_263_ = v___y_291_;
v___y_264_ = v___y_288_;
v___y_265_ = v___y_292_;
v___y_266_ = v___y_290_;
v___y_267_ = v___y_294_;
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
v___y_288_ = v_toCold_300_;
v___y_289_ = v___f_304_;
v___y_290_ = v_suppressElabErrors_302_;
v___y_291_ = v___y_298_;
v___y_292_ = v___y_299_;
v___y_293_ = v_ref_305_;
v___y_294_ = v___x_307_;
goto v___jp_287_;
}
else
{
lean_object* v_val_308_; 
v_val_308_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v___x_306_, 1);
v___y_288_ = v_toCold_300_;
v___y_289_ = v___f_304_;
v___y_290_ = v_suppressElabErrors_302_;
v___y_291_ = v___y_298_;
v___y_292_ = v___y_299_;
v___y_293_ = v_ref_305_;
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
lean_object* v_toCold_544_; lean_object* v_currRecDepth_545_; lean_object* v_ref_546_; uint16_t v_optionFlags_547_; uint8_t v_suppressElabErrors_548_; uint8_t v_checkDeprecated_549_; uint8_t v_isRecordingDeps_550_; lean_object* v_ref_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_toCold_544_ = lean_ctor_get(v___y_541_, 0);
v_currRecDepth_545_ = lean_ctor_get(v___y_541_, 1);
v_ref_546_ = lean_ctor_get(v___y_541_, 2);
v_optionFlags_547_ = lean_ctor_get_uint16(v___y_541_, sizeof(void*)*3);
v_suppressElabErrors_548_ = lean_ctor_get_uint8(v___y_541_, sizeof(void*)*3 + 2);
v_checkDeprecated_549_ = lean_ctor_get_uint8(v___y_541_, sizeof(void*)*3 + 3);
v_isRecordingDeps_550_ = lean_ctor_get_uint8(v___y_541_, sizeof(void*)*3 + 4);
v_ref_551_ = l_Lean_replaceRef(v_ref_537_, v_ref_546_);
lean_inc(v_currRecDepth_545_);
lean_inc_ref(v_toCold_544_);
v___x_552_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_552_, 0, v_toCold_544_);
lean_ctor_set(v___x_552_, 1, v_currRecDepth_545_);
lean_ctor_set(v___x_552_, 2, v_ref_551_);
lean_ctor_set_uint16(v___x_552_, sizeof(void*)*3, v_optionFlags_547_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*3 + 2, v_suppressElabErrors_548_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*3 + 3, v_checkDeprecated_549_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*3 + 4, v_isRecordingDeps_550_);
v___x_553_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_538_, v___y_539_, v___y_540_, v___x_552_, v___y_542_);
lean_dec_ref_known(v___x_552_, 3);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object* v_ref_554_, lean_object* v_msg_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_554_, v_msg_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v_ref_554_);
return v_res_561_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__1(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__0));
v___x_564_ = l_Lean_stringToMessageData(v___x_563_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__3(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__2));
v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__5(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__4));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__9(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__8));
v___x_576_ = l_Lean_stringToMessageData(v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__12(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__11));
v___x_581_ = l_Lean_MessageData_ofFormat(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object* v_funName_582_, lean_object* v_extraParams_583_, lean_object* v_tb_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
uint8_t v_synthetic_590_; 
v_synthetic_590_ = lean_ctor_get_uint8(v_tb_584_, sizeof(void*)*3 + 1);
if (v_synthetic_590_ == 0)
{
lean_object* v_ref_591_; lean_object* v_vars_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_ref_591_ = lean_ctor_get(v_tb_584_, 0);
v_vars_592_ = lean_ctor_get(v_tb_584_, 1);
v___x_593_ = lean_array_get_size(v_vars_592_);
v___x_594_ = lean_nat_dec_lt(v_extraParams_583_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v_extraParams_583_);
lean_dec(v_funName_582_);
v___x_595_ = lean_box(0);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_msg_607_; lean_object* v___x_608_; lean_object* v_ident_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_597_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_593_);
v___x_598_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__1, &l_Lean_Elab_TerminationBy_checkVars___closed__1_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__1);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
lean_inc(v_funName_582_);
v___x_600_ = l_Lean_MessageData_ofName(v_funName_582_);
v___x_601_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__3, &l_Lean_Elab_TerminationBy_checkVars___closed__3_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__3);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_583_);
v___x_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__5, &l_Lean_Elab_TerminationBy_checkVars___closed__5_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__5);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v_msg_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_607_, 0, v___x_599_);
lean_ctor_set(v_msg_607_, 1, v___x_606_);
v___x_608_ = lean_unsigned_to_nat(0u);
v_ident_609_ = lean_array_fget_borrowed(v_vars_592_, v___x_608_);
v___x_610_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__7));
lean_inc(v_ident_609_);
v___x_611_ = l_Lean_Syntax_isOfKind(v_ident_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_dec(v_funName_582_);
v___x_612_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_591_, v_msg_607_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = l_Lean_TSyntax_getId(v_ident_609_);
v___x_614_ = l_Lean_Name_isSuffixOf(v___x_613_, v_funName_582_);
lean_dec(v_funName_582_);
lean_dec(v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_591_, v_msg_607_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_msg_619_; lean_object* v___x_620_; 
v___x_616_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__9, &l_Lean_Elab_TerminationBy_checkVars___closed__9_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__9);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v_msg_607_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__12, &l_Lean_Elab_TerminationBy_checkVars___closed__12_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__12);
v_msg_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_619_, 0, v___x_617_);
lean_ctor_set(v_msg_619_, 1, v___x_618_);
v___x_620_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_591_, v_msg_619_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
return v___x_620_;
}
}
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v_extraParams_583_);
lean_dec(v_funName_582_);
v___x_621_ = lean_box(0);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object* v_funName_623_, lean_object* v_extraParams_624_, lean_object* v_tb_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_Elab_TerminationBy_checkVars(v_funName_623_, v_extraParams_624_, v_tb_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec_ref(v_tb_625_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_object* v_00_u03b1_632_, lean_object* v_ref_633_, lean_object* v_msg_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_633_, v_msg_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object* v_00_u03b1_641_, lean_object* v_ref_642_, lean_object* v_msg_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(v_00_u03b1_641_, v_ref_642_, v_msg_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v_ref_642_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_object* v_00_u03b1_650_, lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_658_, lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_658_, v_msg_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object* v_val_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v_val_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object* v_stx_668_, lean_object* v_terminationBy_x3f_x3f_669_, lean_object* v_terminationBy_x3f_670_, lean_object* v_partialFixpoint_x3f_671_, lean_object* v___x_672_, uint8_t v___x_673_, lean_object* v_toPure_674_, lean_object* v_decreasingBy_x3f_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_676_, 0, v_stx_668_);
lean_ctor_set(v___x_676_, 1, v_terminationBy_x3f_x3f_669_);
lean_ctor_set(v___x_676_, 2, v_terminationBy_x3f_670_);
lean_ctor_set(v___x_676_, 3, v_partialFixpoint_x3f_671_);
lean_ctor_set(v___x_676_, 4, v_decreasingBy_x3f_675_);
lean_ctor_set(v___x_676_, 5, v___x_672_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*6, v___x_673_);
v___x_677_ = lean_apply_2(v_toPure_674_, lean_box(0), v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed(lean_object* v_stx_678_, lean_object* v_terminationBy_x3f_x3f_679_, lean_object* v_terminationBy_x3f_680_, lean_object* v_partialFixpoint_x3f_681_, lean_object* v___x_682_, lean_object* v___x_683_, lean_object* v_toPure_684_, lean_object* v_decreasingBy_x3f_685_){
_start:
{
uint8_t v___x_2906__boxed_686_; lean_object* v_res_687_; 
v___x_2906__boxed_686_ = lean_unbox(v___x_683_);
v_res_687_ = l_Lean_Elab_elabTerminationHints___redArg___lam__1(v_stx_678_, v_terminationBy_x3f_x3f_679_, v_terminationBy_x3f_680_, v_partialFixpoint_x3f_681_, v___x_682_, v___x_2906__boxed_686_, v_toPure_684_, v_decreasingBy_x3f_685_);
return v_res_687_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* v_stx_692_, lean_object* v_terminationBy_x3f_x3f_693_, lean_object* v_terminationBy_x3f_694_, lean_object* v___x_695_, uint8_t v___x_696_, lean_object* v_toPure_697_, lean_object* v_d_x3f_698_, lean_object* v_toBind_699_, lean_object* v_toFunctor_700_, lean_object* v___f_701_, lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v___x_707_, lean_object* v_partialFixpoint_x3f_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___f_710_; 
v___x_709_ = lean_box(v___x_696_);
lean_inc(v_toPure_697_);
v___f_710_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_710_, 0, v_stx_692_);
lean_closure_set(v___f_710_, 1, v_terminationBy_x3f_x3f_693_);
lean_closure_set(v___f_710_, 2, v_terminationBy_x3f_694_);
lean_closure_set(v___f_710_, 3, v_partialFixpoint_x3f_708_);
lean_closure_set(v___f_710_, 4, v___x_695_);
lean_closure_set(v___f_710_, 5, v___x_709_);
lean_closure_set(v___f_710_, 6, v_toPure_697_);
if (lean_obj_tag(v_d_x3f_698_) == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec_ref(v_inst_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v___x_704_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_702_);
lean_dec_ref(v___f_701_);
lean_dec_ref(v_toFunctor_700_);
v___x_711_ = lean_box(0);
v___x_712_ = lean_apply_2(v_toPure_697_, lean_box(0), v___x_711_);
v___x_713_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_712_, v___f_710_);
return v___x_713_;
}
else
{
lean_object* v_val_714_; lean_object* v_map_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_733_; 
v_val_714_ = lean_ctor_get(v_d_x3f_698_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v_d_x3f_698_, 1);
v_map_715_ = lean_ctor_get(v_toFunctor_700_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_toFunctor_700_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v_toFunctor_700_, 1);
lean_dec(v_unused_734_);
v___x_717_ = v_toFunctor_700_;
v_isShared_718_ = v_isSharedCheck_733_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_map_715_);
lean_dec(v_toFunctor_700_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_733_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___y_720_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_723_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0));
v___x_724_ = l_Lean_Name_mkStr4(v___x_702_, v___x_703_, v___x_704_, v___x_723_);
lean_inc(v_val_714_);
v___x_725_ = l_Lean_Syntax_isOfKind(v_val_714_, v___x_724_);
lean_dec(v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_del_object(v___x_717_);
lean_dec(v_toPure_697_);
v___x_726_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2, &l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2);
v___x_727_ = l_Lean_throwErrorAt___redArg(v_inst_705_, v_inst_706_, v_val_714_, v___x_726_);
v___y_720_ = v___x_727_;
goto v___jp_719_;
}
else
{
lean_object* v_tactic_728_; lean_object* v___x_730_; 
lean_dec_ref(v_inst_706_);
lean_dec_ref(v_inst_705_);
v_tactic_728_ = l_Lean_Syntax_getArg(v_val_714_, v___x_707_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v_tactic_728_);
lean_ctor_set(v___x_717_, 0, v_val_714_);
v___x_730_ = v___x_717_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_val_714_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_tactic_728_);
v___x_730_ = v_reuseFailAlloc_732_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_731_; 
v___x_731_ = lean_apply_2(v_toPure_697_, lean_box(0), v___x_730_);
v___y_720_ = v___x_731_;
goto v___jp_719_;
}
}
v___jp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_apply_4(v_map_715_, lean_box(0), lean_box(0), v___f_701_, v___y_720_);
v___x_722_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_721_, v___f_710_);
return v___x_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_stx_735_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_736_ = _args[1];
lean_object* v_terminationBy_x3f_737_ = _args[2];
lean_object* v___x_738_ = _args[3];
lean_object* v___x_739_ = _args[4];
lean_object* v_toPure_740_ = _args[5];
lean_object* v_d_x3f_741_ = _args[6];
lean_object* v_toBind_742_ = _args[7];
lean_object* v_toFunctor_743_ = _args[8];
lean_object* v___f_744_ = _args[9];
lean_object* v___x_745_ = _args[10];
lean_object* v___x_746_ = _args[11];
lean_object* v___x_747_ = _args[12];
lean_object* v_inst_748_ = _args[13];
lean_object* v_inst_749_ = _args[14];
lean_object* v___x_750_ = _args[15];
lean_object* v_partialFixpoint_x3f_751_ = _args[16];
_start:
{
uint8_t v___x_2924__boxed_752_; lean_object* v_res_753_; 
v___x_2924__boxed_752_ = lean_unbox(v___x_739_);
v_res_753_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_735_, v_terminationBy_x3f_x3f_736_, v_terminationBy_x3f_737_, v___x_738_, v___x_2924__boxed_752_, v_toPure_740_, v_d_x3f_741_, v_toBind_742_, v_toFunctor_743_, v___f_744_, v___x_745_, v___x_746_, v___x_747_, v_inst_748_, v_inst_749_, v___x_750_, v_partialFixpoint_x3f_751_);
lean_dec(v___x_750_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object* v___f_754_, lean_object* v_partialFixpoint_x3f_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_apply_1(v___f_754_, v_partialFixpoint_x3f_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object* v_stx_760_, lean_object* v_terminationBy_x3f_x3f_761_, lean_object* v___x_762_, uint8_t v___x_763_, lean_object* v_toPure_764_, lean_object* v_d_x3f_765_, lean_object* v_toBind_766_, lean_object* v_toFunctor_767_, lean_object* v___f_768_, lean_object* v___x_769_, lean_object* v___x_770_, lean_object* v___x_771_, lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v___x_774_, lean_object* v_t_x3f_775_, lean_object* v_terminationBy_x3f_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___f_778_; 
v___x_777_ = lean_box(v___x_763_);
lean_inc(v___x_774_);
lean_inc_ref(v___x_771_);
lean_inc_ref(v___x_770_);
lean_inc_ref(v___x_769_);
lean_inc(v_toBind_766_);
lean_inc(v_toPure_764_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed), 17, 16);
lean_closure_set(v___f_778_, 0, v_stx_760_);
lean_closure_set(v___f_778_, 1, v_terminationBy_x3f_x3f_761_);
lean_closure_set(v___f_778_, 2, v_terminationBy_x3f_776_);
lean_closure_set(v___f_778_, 3, v___x_762_);
lean_closure_set(v___f_778_, 4, v___x_777_);
lean_closure_set(v___f_778_, 5, v_toPure_764_);
lean_closure_set(v___f_778_, 6, v_d_x3f_765_);
lean_closure_set(v___f_778_, 7, v_toBind_766_);
lean_closure_set(v___f_778_, 8, v_toFunctor_767_);
lean_closure_set(v___f_778_, 9, v___f_768_);
lean_closure_set(v___f_778_, 10, v___x_769_);
lean_closure_set(v___f_778_, 11, v___x_770_);
lean_closure_set(v___f_778_, 12, v___x_771_);
lean_closure_set(v___f_778_, 13, v_inst_772_);
lean_closure_set(v___f_778_, 14, v_inst_773_);
lean_closure_set(v___f_778_, 15, v___x_774_);
if (lean_obj_tag(v_t_x3f_775_) == 1)
{
lean_object* v_val_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_856_; 
v_val_779_ = lean_ctor_get(v_t_x3f_775_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_t_x3f_775_);
if (v_isSharedCheck_856_ == 0)
{
v___x_781_ = v_t_x3f_775_;
v_isShared_782_ = v_isSharedCheck_856_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_val_779_);
lean_dec(v_t_x3f_775_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_856_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_783_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_771_);
lean_inc_ref(v___x_770_);
lean_inc_ref(v___x_769_);
v___x_784_ = l_Lean_Name_mkStr4(v___x_769_, v___x_770_, v___x_771_, v___x_783_);
lean_inc(v_val_779_);
v___x_785_ = l_Lean_Syntax_isOfKind(v_val_779_, v___x_784_);
lean_dec(v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_786_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_771_);
lean_inc_ref(v___x_770_);
lean_inc_ref(v___x_769_);
v___x_787_ = l_Lean_Name_mkStr4(v___x_769_, v___x_770_, v___x_771_, v___x_786_);
lean_inc(v_val_779_);
v___x_788_ = l_Lean_Syntax_isOfKind(v_val_779_, v___x_787_);
lean_dec(v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_789_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_790_ = l_Lean_Name_mkStr4(v___x_769_, v___x_770_, v___x_771_, v___x_789_);
lean_inc(v_val_779_);
v___x_791_ = l_Lean_Syntax_isOfKind(v_val_779_, v___x_790_);
lean_dec(v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_del_object(v___x_781_);
lean_dec(v_val_779_);
lean_dec(v___x_774_);
v___f_792_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_792_, 0, v___f_778_);
v___x_793_ = lean_box(0);
v___x_794_ = lean_apply_2(v_toPure_764_, lean_box(0), v___x_793_);
v___x_795_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v___x_794_, v___f_792_);
return v___x_795_;
}
else
{
lean_object* v___f_796_; lean_object* v_term_x3f_798_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___f_796_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_796_, 0, v___f_778_);
v___x_806_ = l_Lean_Syntax_getArg(v_val_779_, v___x_774_);
v___x_807_ = l_Lean_Syntax_isNone(v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_806_);
v___x_809_ = l_Lean_Syntax_matchesNull(v___x_806_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v___x_806_);
lean_del_object(v___x_781_);
lean_dec(v_val_779_);
lean_dec(v___x_774_);
v___x_810_ = lean_box(0);
v___x_811_ = lean_apply_2(v_toPure_764_, lean_box(0), v___x_810_);
v___x_812_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v___x_811_, v___f_796_);
return v___x_812_;
}
else
{
lean_object* v_term_x3f_813_; lean_object* v___x_814_; 
v_term_x3f_813_ = l_Lean_Syntax_getArg(v___x_806_, v___x_774_);
lean_dec(v___x_774_);
lean_dec(v___x_806_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v_term_x3f_813_);
v_term_x3f_798_ = v___x_814_;
goto v___jp_797_;
}
}
else
{
lean_object* v___x_815_; 
lean_dec(v___x_806_);
lean_dec(v___x_774_);
v___x_815_ = lean_box(0);
v_term_x3f_798_ = v___x_815_;
goto v___jp_797_;
}
v___jp_797_:
{
uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_799_ = 2;
v___x_800_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_800_, 0, v_val_779_);
lean_ctor_set(v___x_800_, 1, v_term_x3f_798_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*2, v___x_799_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_800_);
v___x_802_ = v___x_781_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_805_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_apply_2(v_toPure_764_, lean_box(0), v___x_802_);
v___x_804_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v___x_803_, v___f_796_);
return v___x_804_;
}
}
}
}
else
{
lean_object* v___f_816_; lean_object* v_term_x3f_818_; lean_object* v___x_826_; uint8_t v___x_827_; 
lean_dec_ref(v___x_771_);
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_769_);
v___f_816_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_816_, 0, v___f_778_);
v___x_826_ = l_Lean_Syntax_getArg(v_val_779_, v___x_774_);
v___x_827_ = l_Lean_Syntax_isNone(v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_826_);
v___x_829_ = l_Lean_Syntax_matchesNull(v___x_826_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec(v___x_826_);
lean_del_object(v___x_781_);
lean_dec(v_val_779_);
lean_dec(v___x_774_);
v___x_830_ = lean_box(0);
v___x_831_ = lean_apply_2(v_toPure_764_, lean_box(0), v___x_830_);
v___x_832_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v___x_831_, v___f_816_);
return v___x_832_;
}
else
{
lean_object* v_term_x3f_833_; lean_object* v___x_834_; 
v_term_x3f_833_ = l_Lean_Syntax_getArg(v___x_826_, v___x_774_);
lean_dec(v___x_774_);
lean_dec(v___x_826_);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v_term_x3f_833_);
v_term_x3f_818_ = v___x_834_;
goto v___jp_817_;
}
}
else
{
lean_object* v___x_835_; 
lean_dec(v___x_826_);
lean_dec(v___x_774_);
v___x_835_ = lean_box(0);
v_term_x3f_818_ = v___x_835_;
goto v___jp_817_;
}
v___jp_817_:
{
uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_819_ = 1;
v___x_820_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_820_, 0, v_val_779_);
lean_ctor_set(v___x_820_, 1, v_term_x3f_818_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*2, v___x_819_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_820_);
v___x_822_ = v___x_781_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_825_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_apply_2(v_toPure_764_, lean_box(0), v___x_822_);
v___x_824_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v___x_823_, v___f_816_);
return v___x_824_;
}
}
}
}
else
{
lean_object* v___f_836_; lean_object* v_term_x3f_838_; lean_object* v___x_846_; uint8_t v___x_847_; 
lean_dec_ref(v___x_771_);
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_769_);
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_836_, 0, v___f_778_);
v___x_846_ = l_Lean_Syntax_getArg(v_val_779_, v___x_774_);
v___x_847_ = l_Lean_Syntax_isNone(v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_846_);
v___x_849_ = l_Lean_Syntax_matchesNull(v___x_846_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v___x_846_);
lean_del_object(v___x_781_);
lean_dec(v_val_779_);
lean_dec(v___x_774_);
v___x_850_ = lean_box(0);
v___x_851_ = lean_apply_2(v_toPure_764_, lean_box(0), v___x_850_);
v___x_852_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v___x_851_, v___f_836_);
return v___x_852_;
}
else
{
lean_object* v_term_x3f_853_; lean_object* v___x_854_; 
v_term_x3f_853_ = l_Lean_Syntax_getArg(v___x_846_, v___x_774_);
lean_dec(v___x_774_);
lean_dec(v___x_846_);
v___x_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_854_, 0, v_term_x3f_853_);
v_term_x3f_838_ = v___x_854_;
goto v___jp_837_;
}
}
else
{
lean_object* v___x_855_; 
lean_dec(v___x_846_);
lean_dec(v___x_774_);
v___x_855_ = lean_box(0);
v_term_x3f_838_ = v___x_855_;
goto v___jp_837_;
}
v___jp_837_:
{
uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_839_ = 0;
v___x_840_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_840_, 0, v_val_779_);
lean_ctor_set(v___x_840_, 1, v_term_x3f_838_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*2, v___x_839_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_840_);
v___x_842_ = v___x_781_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_845_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_apply_2(v_toPure_764_, lean_box(0), v___x_842_);
v___x_844_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v___x_843_, v___f_836_);
return v___x_844_;
}
}
}
}
}
else
{
lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec(v_t_x3f_775_);
lean_dec(v___x_774_);
lean_dec_ref(v___x_771_);
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_769_);
v___f_857_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_857_, 0, v___f_778_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_apply_2(v_toPure_764_, lean_box(0), v___x_858_);
v___x_860_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v___x_859_, v___f_857_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_stx_861_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_862_ = _args[1];
lean_object* v___x_863_ = _args[2];
lean_object* v___x_864_ = _args[3];
lean_object* v_toPure_865_ = _args[4];
lean_object* v_d_x3f_866_ = _args[5];
lean_object* v_toBind_867_ = _args[6];
lean_object* v_toFunctor_868_ = _args[7];
lean_object* v___f_869_ = _args[8];
lean_object* v___x_870_ = _args[9];
lean_object* v___x_871_ = _args[10];
lean_object* v___x_872_ = _args[11];
lean_object* v_inst_873_ = _args[12];
lean_object* v_inst_874_ = _args[13];
lean_object* v___x_875_ = _args[14];
lean_object* v_t_x3f_876_ = _args[15];
lean_object* v_terminationBy_x3f_877_ = _args[16];
_start:
{
uint8_t v___x_3013__boxed_878_; lean_object* v_res_879_; 
v___x_3013__boxed_878_ = lean_unbox(v___x_864_);
v_res_879_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11(v_stx_861_, v_terminationBy_x3f_x3f_862_, v___x_863_, v___x_3013__boxed_878_, v_toPure_865_, v_d_x3f_866_, v_toBind_867_, v_toFunctor_868_, v___f_869_, v___x_870_, v___x_871_, v___x_872_, v_inst_873_, v_inst_874_, v___x_875_, v_t_x3f_876_, v_terminationBy_x3f_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* v___f_880_, lean_object* v_terminationBy_x3f_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = lean_apply_1(v___f_880_, v_terminationBy_x3f_881_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* v_stx_891_, lean_object* v___x_892_, uint8_t v___x_893_, lean_object* v_toPure_894_, lean_object* v_d_x3f_895_, lean_object* v_toBind_896_, lean_object* v_toFunctor_897_, lean_object* v___f_898_, lean_object* v___x_899_, lean_object* v___x_900_, lean_object* v___x_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v___x_904_, lean_object* v_t_x3f_905_, lean_object* v_terminationBy_x3f_x3f_906_){
_start:
{
lean_object* v___x_907_; lean_object* v___f_908_; 
v___x_907_ = lean_box(v___x_893_);
lean_inc(v_t_x3f_905_);
lean_inc(v___x_904_);
lean_inc_ref(v_inst_903_);
lean_inc_ref(v_inst_902_);
lean_inc_ref(v___x_901_);
lean_inc_ref(v___x_900_);
lean_inc_ref(v___x_899_);
lean_inc(v_toBind_896_);
lean_inc(v_toPure_894_);
lean_inc(v___x_892_);
v___f_908_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_908_, 0, v_stx_891_);
lean_closure_set(v___f_908_, 1, v_terminationBy_x3f_x3f_906_);
lean_closure_set(v___f_908_, 2, v___x_892_);
lean_closure_set(v___f_908_, 3, v___x_907_);
lean_closure_set(v___f_908_, 4, v_toPure_894_);
lean_closure_set(v___f_908_, 5, v_d_x3f_895_);
lean_closure_set(v___f_908_, 6, v_toBind_896_);
lean_closure_set(v___f_908_, 7, v_toFunctor_897_);
lean_closure_set(v___f_908_, 8, v___f_898_);
lean_closure_set(v___f_908_, 9, v___x_899_);
lean_closure_set(v___f_908_, 10, v___x_900_);
lean_closure_set(v___f_908_, 11, v___x_901_);
lean_closure_set(v___f_908_, 12, v_inst_902_);
lean_closure_set(v___f_908_, 13, v_inst_903_);
lean_closure_set(v___f_908_, 14, v___x_904_);
lean_closure_set(v___f_908_, 15, v_t_x3f_905_);
if (lean_obj_tag(v_t_x3f_905_) == 1)
{
lean_object* v_val_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_1021_; 
v_val_909_ = lean_ctor_get(v_t_x3f_905_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_t_x3f_905_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_911_ = v_t_x3f_905_;
v_isShared_912_ = v_isSharedCheck_1021_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_val_909_);
lean_dec(v_t_x3f_905_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_1021_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_913_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0));
lean_inc_ref(v___x_901_);
lean_inc_ref(v___x_900_);
lean_inc_ref(v___x_899_);
v___x_914_ = l_Lean_Name_mkStr4(v___x_899_, v___x_900_, v___x_901_, v___x_913_);
lean_inc(v_val_909_);
v___x_915_ = l_Lean_Syntax_isOfKind(v_val_909_, v___x_914_);
lean_dec(v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
lean_del_object(v___x_911_);
lean_dec(v___x_892_);
v___x_916_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1));
lean_inc_ref(v___x_901_);
lean_inc_ref(v___x_900_);
lean_inc_ref(v___x_899_);
v___x_917_ = l_Lean_Name_mkStr4(v___x_899_, v___x_900_, v___x_901_, v___x_916_);
lean_inc(v_val_909_);
v___x_918_ = l_Lean_Syntax_isOfKind(v_val_909_, v___x_917_);
lean_dec(v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_919_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_901_);
lean_inc_ref(v___x_900_);
lean_inc_ref(v___x_899_);
v___x_920_ = l_Lean_Name_mkStr4(v___x_899_, v___x_900_, v___x_901_, v___x_919_);
lean_inc(v_val_909_);
v___x_921_ = l_Lean_Syntax_isOfKind(v_val_909_, v___x_920_);
lean_dec(v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_922_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_901_);
lean_inc_ref(v___x_900_);
lean_inc_ref(v___x_899_);
v___x_923_ = l_Lean_Name_mkStr4(v___x_899_, v___x_900_, v___x_901_, v___x_922_);
lean_inc(v_val_909_);
v___x_924_ = l_Lean_Syntax_isOfKind(v_val_909_, v___x_923_);
lean_dec(v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_925_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_926_ = l_Lean_Name_mkStr4(v___x_899_, v___x_900_, v___x_901_, v___x_925_);
lean_inc(v_val_909_);
v___x_927_ = l_Lean_Syntax_isOfKind(v_val_909_, v___x_926_);
lean_dec(v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___f_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec(v___x_904_);
lean_dec(v_toPure_894_);
v___f_928_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_928_, 0, v___f_908_);
v___x_929_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_930_ = l_Lean_throwErrorAt___redArg(v_inst_902_, v_inst_903_, v_val_909_, v___x_929_);
v___x_931_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_930_, v___f_928_);
return v___x_931_;
}
else
{
lean_object* v___f_932_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___f_932_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_932_, 0, v___f_908_);
v___x_937_ = l_Lean_Syntax_getArg(v_val_909_, v___x_904_);
lean_dec(v___x_904_);
v___x_938_ = l_Lean_Syntax_isNone(v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_unsigned_to_nat(2u);
v___x_940_ = l_Lean_Syntax_matchesNull(v___x_937_, v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_toPure_894_);
v___x_941_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_942_ = l_Lean_throwErrorAt___redArg(v_inst_902_, v_inst_903_, v_val_909_, v___x_941_);
v___x_943_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_942_, v___f_932_);
return v___x_943_;
}
else
{
lean_dec(v_val_909_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
goto v___jp_933_;
}
}
else
{
lean_dec(v___x_937_);
lean_dec(v_val_909_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
goto v___jp_933_;
}
v___jp_933_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_box(0);
v___x_935_ = lean_apply_2(v_toPure_894_, lean_box(0), v___x_934_);
v___x_936_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_935_, v___f_932_);
return v___x_936_;
}
}
}
else
{
lean_object* v___f_944_; lean_object* v___x_949_; uint8_t v___x_950_; 
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v___x_899_);
v___f_944_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_944_, 0, v___f_908_);
v___x_949_ = l_Lean_Syntax_getArg(v_val_909_, v___x_904_);
lean_dec(v___x_904_);
v___x_950_ = l_Lean_Syntax_isNone(v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = lean_unsigned_to_nat(2u);
v___x_952_ = l_Lean_Syntax_matchesNull(v___x_949_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v_toPure_894_);
v___x_953_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_954_ = l_Lean_throwErrorAt___redArg(v_inst_902_, v_inst_903_, v_val_909_, v___x_953_);
v___x_955_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_954_, v___f_944_);
return v___x_955_;
}
else
{
lean_dec(v_val_909_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
goto v___jp_945_;
}
}
else
{
lean_dec(v___x_949_);
lean_dec(v_val_909_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
goto v___jp_945_;
}
v___jp_945_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = lean_box(0);
v___x_947_ = lean_apply_2(v_toPure_894_, lean_box(0), v___x_946_);
v___x_948_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_947_, v___f_944_);
return v___x_948_;
}
}
}
else
{
lean_object* v___f_956_; lean_object* v___x_961_; uint8_t v___x_962_; 
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v___x_899_);
v___f_956_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_956_, 0, v___f_908_);
v___x_961_ = l_Lean_Syntax_getArg(v_val_909_, v___x_904_);
lean_dec(v___x_904_);
v___x_962_ = l_Lean_Syntax_isNone(v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_unsigned_to_nat(2u);
v___x_964_ = l_Lean_Syntax_matchesNull(v___x_961_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v_toPure_894_);
v___x_965_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_966_ = l_Lean_throwErrorAt___redArg(v_inst_902_, v_inst_903_, v_val_909_, v___x_965_);
v___x_967_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_966_, v___f_956_);
return v___x_967_;
}
else
{
lean_dec(v_val_909_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
goto v___jp_957_;
}
}
else
{
lean_dec(v___x_961_);
lean_dec(v_val_909_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
goto v___jp_957_;
}
v___jp_957_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_box(0);
v___x_959_ = lean_apply_2(v_toPure_894_, lean_box(0), v___x_958_);
v___x_960_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_959_, v___f_956_);
return v___x_960_;
}
}
}
else
{
lean_object* v___f_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec(v_val_909_);
lean_dec(v___x_904_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v___x_899_);
v___f_968_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_968_, 0, v___f_908_);
v___x_969_ = lean_box(0);
v___x_970_ = lean_apply_2(v_toPure_894_, lean_box(0), v___x_969_);
v___x_971_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_970_, v___f_968_);
return v___x_971_;
}
}
else
{
lean_object* v___f_972_; lean_object* v___y_974_; uint8_t v___y_975_; lean_object* v___y_976_; uint8_t v___y_977_; lean_object* v___y_985_; uint8_t v___y_986_; uint8_t v___y_987_; lean_object* v_s_994_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v___x_899_);
v___f_972_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_972_, 0, v___f_908_);
v___x_1012_ = l_Lean_Syntax_getArg(v_val_909_, v___x_904_);
v___x_1013_ = l_Lean_Syntax_isNone(v___x_1012_);
if (v___x_1013_ == 0)
{
uint8_t v___x_1014_; 
lean_inc(v___x_1012_);
v___x_1014_ = l_Lean_Syntax_matchesNull(v___x_1012_, v___x_904_);
lean_dec(v___x_904_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v___x_1012_);
lean_del_object(v___x_911_);
lean_dec(v_toPure_894_);
lean_dec(v___x_892_);
v___x_1015_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1016_ = l_Lean_throwErrorAt___redArg(v_inst_902_, v_inst_903_, v_val_909_, v___x_1015_);
v___x_1017_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_1016_, v___f_972_);
return v___x_1017_;
}
else
{
lean_object* v_s_1018_; lean_object* v___x_1019_; 
v_s_1018_ = l_Lean_Syntax_getArg(v___x_1012_, v___x_892_);
lean_dec(v___x_1012_);
v___x_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_s_1018_);
v_s_994_ = v___x_1019_;
goto v___jp_993_;
}
}
else
{
lean_object* v___x_1020_; 
lean_dec(v___x_1012_);
lean_dec(v___x_904_);
v___x_1020_ = lean_box(0);
v_s_994_ = v___x_1020_;
goto v___jp_993_;
}
v___jp_973_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_978_, 0, v_val_909_);
lean_ctor_set(v___x_978_, 1, v___y_974_);
lean_ctor_set(v___x_978_, 2, v___y_976_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*3, v___y_977_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*3 + 1, v___y_975_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_978_);
v___x_980_ = v___x_911_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_983_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_apply_2(v_toPure_894_, lean_box(0), v___x_980_);
v___x_982_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_981_, v___f_972_);
return v___x_982_;
}
}
v___jp_984_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_988_ = lean_mk_empty_array_with_capacity(v___x_892_);
lean_dec(v___x_892_);
v___x_989_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_989_, 0, v_val_909_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
lean_ctor_set(v___x_989_, 2, v___y_985_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*3, v___y_987_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*3 + 1, v___y_986_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
v___x_991_ = lean_apply_2(v_toPure_894_, lean_box(0), v___x_990_);
v___x_992_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_991_, v___f_972_);
return v___x_992_;
}
v___jp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_995_ = lean_unsigned_to_nat(2u);
v___x_996_ = l_Lean_Syntax_getArg(v_val_909_, v___x_995_);
lean_inc(v___x_996_);
v___x_997_ = l_Lean_Syntax_matchesNull(v___x_996_, v___x_995_);
if (v___x_997_ == 0)
{
uint8_t v___x_998_; 
lean_del_object(v___x_911_);
v___x_998_ = l_Lean_Syntax_matchesNull(v___x_996_, v___x_892_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec(v_s_994_);
lean_dec(v_toPure_894_);
lean_dec(v___x_892_);
v___x_999_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1000_ = l_Lean_throwErrorAt___redArg(v_inst_902_, v_inst_903_, v_val_909_, v___x_999_);
v___x_1001_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_1000_, v___f_972_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v_body_1003_; 
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
v___x_1002_ = lean_unsigned_to_nat(3u);
v_body_1003_ = l_Lean_Syntax_getArg(v_val_909_, v___x_1002_);
if (lean_obj_tag(v_s_994_) == 0)
{
v___y_985_ = v_body_1003_;
v___y_986_ = v___x_997_;
v___y_987_ = v___x_997_;
goto v___jp_984_;
}
else
{
lean_dec_ref_known(v_s_994_, 1);
v___y_985_ = v_body_1003_;
v___y_986_ = v___x_997_;
v___y_987_ = v___x_998_;
goto v___jp_984_;
}
}
}
else
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = l_Lean_Syntax_getArg(v___x_996_, v___x_892_);
lean_dec(v___x_996_);
lean_inc(v___x_1004_);
v___x_1005_ = l_Lean_Syntax_matchesNull(v___x_1004_, v___x_892_);
lean_dec(v___x_892_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v_body_1007_; lean_object* v_vars_1008_; 
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
v___x_1006_ = lean_unsigned_to_nat(3u);
v_body_1007_ = l_Lean_Syntax_getArg(v_val_909_, v___x_1006_);
v_vars_1008_ = l_Lean_Syntax_getArgs(v___x_1004_);
lean_dec(v___x_1004_);
if (lean_obj_tag(v_s_994_) == 0)
{
v___y_974_ = v_vars_1008_;
v___y_975_ = v___x_1005_;
v___y_976_ = v_body_1007_;
v___y_977_ = v___x_1005_;
goto v___jp_973_;
}
else
{
lean_dec_ref_known(v_s_994_, 1);
v___y_974_ = v_vars_1008_;
v___y_975_ = v___x_1005_;
v___y_976_ = v_body_1007_;
v___y_977_ = v___x_997_;
goto v___jp_973_;
}
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec(v___x_1004_);
lean_dec(v_s_994_);
lean_del_object(v___x_911_);
lean_dec(v_toPure_894_);
v___x_1009_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
v___x_1010_ = l_Lean_throwErrorAt___redArg(v_inst_902_, v_inst_903_, v_val_909_, v___x_1009_);
v___x_1011_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_1010_, v___f_972_);
return v___x_1011_;
}
}
}
}
}
}
else
{
lean_object* v___f_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_dec(v_t_x3f_905_);
lean_dec(v___x_904_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v___x_899_);
lean_dec(v___x_892_);
v___f_1022_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1022_, 0, v___f_908_);
v___x_1023_ = lean_box(0);
v___x_1024_ = lean_apply_2(v_toPure_894_, lean_box(0), v___x_1023_);
v___x_1025_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_1024_, v___f_1022_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed(lean_object* v_stx_1026_, lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v_toPure_1029_, lean_object* v_d_x3f_1030_, lean_object* v_toBind_1031_, lean_object* v_toFunctor_1032_, lean_object* v___f_1033_, lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v___x_1039_, lean_object* v_t_x3f_1040_, lean_object* v_terminationBy_x3f_x3f_1041_){
_start:
{
uint8_t v___x_3237__boxed_1042_; lean_object* v_res_1043_; 
v___x_3237__boxed_1042_ = lean_unbox(v___x_1028_);
v_res_1043_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19(v_stx_1026_, v___x_1027_, v___x_3237__boxed_1042_, v_toPure_1029_, v_d_x3f_1030_, v_toBind_1031_, v_toFunctor_1032_, v___f_1033_, v___x_1034_, v___x_1035_, v___x_1036_, v_inst_1037_, v_inst_1038_, v___x_1039_, v_t_x3f_1040_, v_terminationBy_x3f_x3f_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* v___f_1044_, lean_object* v_terminationBy_x3f_x3f_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_apply_1(v___f_1044_, v_terminationBy_x3f_x3f_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_stx_1071_){
_start:
{
if (lean_obj_tag(v_stx_1071_) == 0)
{
lean_object* v_toApplicative_1072_; lean_object* v_toPure_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_toApplicative_1072_ = lean_ctor_get(v_inst_1069_, 0);
lean_inc_ref(v_toApplicative_1072_);
lean_dec_ref(v_inst_1070_);
lean_dec_ref(v_inst_1069_);
v_toPure_1073_ = lean_ctor_get(v_toApplicative_1072_, 1);
lean_inc(v_toPure_1073_);
lean_dec_ref(v_toApplicative_1072_);
v___x_1074_ = 1;
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1077_, 0, v_stx_1071_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
lean_ctor_set(v___x_1077_, 2, v___x_1076_);
lean_ctor_set(v___x_1077_, 3, v___x_1076_);
lean_ctor_set(v___x_1077_, 4, v___x_1076_);
lean_ctor_set(v___x_1077_, 5, v___x_1075_);
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*6, v___x_1074_);
v___x_1078_ = lean_apply_2(v_toPure_1073_, lean_box(0), v___x_1077_);
return v___x_1078_;
}
else
{
lean_object* v_toApplicative_1079_; lean_object* v_toBind_1080_; lean_object* v_toFunctor_1081_; lean_object* v_toPure_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v_toApplicative_1079_ = lean_ctor_get(v_inst_1069_, 0);
v_toBind_1080_ = lean_ctor_get(v_inst_1069_, 1);
v_toFunctor_1081_ = lean_ctor_get(v_toApplicative_1079_, 0);
v_toPure_1082_ = lean_ctor_get(v_toApplicative_1079_, 1);
v___x_1083_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__0));
v___x_1084_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__1));
v___x_1085_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__2));
v___x_1086_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__4));
lean_inc(v_stx_1071_);
v___x_1087_ = l_Lean_Syntax_isOfKind(v_stx_1071_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1088_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1089_ = lean_box(0);
lean_inc_n(v_stx_1071_, 2);
v___x_1090_ = l_Lean_Syntax_formatStx(v_stx_1071_, v___x_1089_, v___x_1087_);
v___x_1091_ = l_Std_Format_defWidth;
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = l_Std_Format_pretty(v___x_1090_, v___x_1091_, v___x_1092_, v___x_1092_);
v___x_1094_ = lean_string_append(v___x_1088_, v___x_1093_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1096_ = lean_string_append(v___x_1094_, v___x_1095_);
v___x_1097_ = l_Lean_Syntax_getKind(v_stx_1071_);
v___x_1098_ = 1;
v___x_1099_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1097_, v___x_1098_);
v___x_1100_ = lean_string_append(v___x_1096_, v___x_1099_);
lean_dec_ref(v___x_1099_);
v___x_1101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
v___x_1102_ = l_Lean_MessageData_ofFormat(v___x_1101_);
v___x_1103_ = l_Lean_throwErrorAt___redArg(v_inst_1069_, v_inst_1070_, v_stx_1071_, v___x_1102_);
return v___x_1103_;
}
else
{
lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v_d_x3f_1109_; lean_object* v_t_x3f_1134_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___f_1104_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__7));
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1172_ = l_Lean_Syntax_getArg(v_stx_1071_, v___x_1105_);
v___x_1173_ = l_Lean_Syntax_isNone(v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1172_);
v___x_1175_ = l_Lean_Syntax_matchesNull(v___x_1172_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec(v___x_1172_);
v___x_1176_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1177_ = lean_box(0);
lean_inc_n(v_stx_1071_, 2);
v___x_1178_ = l_Lean_Syntax_formatStx(v_stx_1071_, v___x_1177_, v___x_1175_);
v___x_1179_ = l_Std_Format_defWidth;
v___x_1180_ = l_Std_Format_pretty(v___x_1178_, v___x_1179_, v___x_1105_, v___x_1105_);
v___x_1181_ = lean_string_append(v___x_1176_, v___x_1180_);
lean_dec_ref(v___x_1180_);
v___x_1182_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1183_ = lean_string_append(v___x_1181_, v___x_1182_);
v___x_1184_ = l_Lean_Syntax_getKind(v_stx_1071_);
v___x_1185_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1184_, v___x_1087_);
v___x_1186_ = lean_string_append(v___x_1183_, v___x_1185_);
lean_dec_ref(v___x_1185_);
v___x_1187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
v___x_1188_ = l_Lean_MessageData_ofFormat(v___x_1187_);
v___x_1189_ = l_Lean_throwErrorAt___redArg(v_inst_1069_, v_inst_1070_, v_stx_1071_, v___x_1188_);
return v___x_1189_;
}
else
{
lean_object* v_t_x3f_1190_; lean_object* v___x_1191_; 
v_t_x3f_1190_ = l_Lean_Syntax_getArg(v___x_1172_, v___x_1105_);
lean_dec(v___x_1172_);
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_t_x3f_1190_);
v_t_x3f_1134_ = v___x_1191_;
goto v___jp_1133_;
}
}
else
{
lean_object* v___x_1192_; 
lean_dec(v___x_1172_);
v___x_1192_ = lean_box(0);
v_t_x3f_1134_ = v___x_1192_;
goto v___jp_1133_;
}
v___jp_1106_:
{
lean_object* v___x_1110_; lean_object* v___f_1111_; 
v___x_1110_ = lean_box(v___x_1087_);
lean_inc(v___y_1107_);
lean_inc(v_toBind_1080_);
lean_inc(v_toPure_1082_);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed), 16, 15);
lean_closure_set(v___f_1111_, 0, v_stx_1071_);
lean_closure_set(v___f_1111_, 1, v___x_1105_);
lean_closure_set(v___f_1111_, 2, v___x_1110_);
lean_closure_set(v___f_1111_, 3, v_toPure_1082_);
lean_closure_set(v___f_1111_, 4, v_d_x3f_1109_);
lean_closure_set(v___f_1111_, 5, v_toBind_1080_);
lean_closure_set(v___f_1111_, 6, v_toFunctor_1081_);
lean_closure_set(v___f_1111_, 7, v___f_1104_);
lean_closure_set(v___f_1111_, 8, v___x_1083_);
lean_closure_set(v___f_1111_, 9, v___x_1084_);
lean_closure_set(v___f_1111_, 10, v___x_1085_);
lean_closure_set(v___f_1111_, 11, v_inst_1069_);
lean_closure_set(v___f_1111_, 12, v_inst_1070_);
lean_closure_set(v___f_1111_, 13, v___y_1108_);
lean_closure_set(v___f_1111_, 14, v___y_1107_);
if (lean_obj_tag(v___y_1107_) == 1)
{
lean_object* v_val_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1128_; 
v_val_1112_ = lean_ctor_get(v___y_1107_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___y_1107_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1114_ = v___y_1107_;
v_isShared_1115_ = v_isSharedCheck_1128_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_val_1112_);
lean_dec(v___y_1107_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1128_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__8));
lean_inc(v_val_1112_);
v___x_1117_ = l_Lean_Syntax_isOfKind(v_val_1112_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___f_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_del_object(v___x_1114_);
lean_dec(v_val_1112_);
v___f_1118_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1118_, 0, v___f_1111_);
v___x_1119_ = lean_box(0);
v___x_1120_ = lean_apply_2(v_toPure_1082_, lean_box(0), v___x_1119_);
v___x_1121_ = lean_apply_4(v_toBind_1080_, lean_box(0), lean_box(0), v___x_1120_, v___f_1118_);
return v___x_1121_;
}
else
{
lean_object* v___f_1122_; lean_object* v___x_1124_; 
v___f_1122_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1122_, 0, v___f_1111_);
if (v_isShared_1115_ == 0)
{
v___x_1124_ = v___x_1114_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_val_1112_);
v___x_1124_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_apply_2(v_toPure_1082_, lean_box(0), v___x_1124_);
v___x_1126_ = lean_apply_4(v_toBind_1080_, lean_box(0), lean_box(0), v___x_1125_, v___f_1122_);
return v___x_1126_;
}
}
}
}
else
{
lean_object* v___f_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec(v___y_1107_);
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1129_, 0, v___f_1111_);
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_apply_2(v_toPure_1082_, lean_box(0), v___x_1130_);
v___x_1132_ = lean_apply_4(v_toBind_1080_, lean_box(0), lean_box(0), v___x_1131_, v___f_1129_);
return v___x_1132_;
}
}
v___jp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1135_ = lean_unsigned_to_nat(1u);
v___x_1136_ = l_Lean_Syntax_getArg(v_stx_1071_, v___x_1135_);
v___x_1137_ = l_Lean_Syntax_isNone(v___x_1136_);
if (v___x_1137_ == 0)
{
uint8_t v___x_1138_; 
lean_inc(v___x_1136_);
v___x_1138_ = l_Lean_Syntax_matchesNull(v___x_1136_, v___x_1135_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec(v___x_1136_);
lean_dec(v_t_x3f_1134_);
v___x_1139_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1140_ = lean_box(0);
lean_inc_n(v_stx_1071_, 2);
v___x_1141_ = l_Lean_Syntax_formatStx(v_stx_1071_, v___x_1140_, v___x_1138_);
v___x_1142_ = l_Std_Format_defWidth;
v___x_1143_ = l_Std_Format_pretty(v___x_1141_, v___x_1142_, v___x_1105_, v___x_1105_);
v___x_1144_ = lean_string_append(v___x_1139_, v___x_1143_);
lean_dec_ref(v___x_1143_);
v___x_1145_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1146_ = lean_string_append(v___x_1144_, v___x_1145_);
v___x_1147_ = l_Lean_Syntax_getKind(v_stx_1071_);
v___x_1148_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1147_, v___x_1087_);
v___x_1149_ = lean_string_append(v___x_1146_, v___x_1148_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
v___x_1151_ = l_Lean_MessageData_ofFormat(v___x_1150_);
v___x_1152_ = l_Lean_throwErrorAt___redArg(v_inst_1069_, v_inst_1070_, v_stx_1071_, v___x_1151_);
return v___x_1152_;
}
else
{
lean_object* v_d_x3f_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v_d_x3f_1153_ = l_Lean_Syntax_getArg(v___x_1136_, v___x_1105_);
lean_dec(v___x_1136_);
v___x_1154_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__9));
lean_inc(v_d_x3f_1153_);
v___x_1155_ = l_Lean_Syntax_isOfKind(v_d_x3f_1153_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec(v_d_x3f_1153_);
lean_dec(v_t_x3f_1134_);
v___x_1156_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1157_ = lean_box(0);
lean_inc_n(v_stx_1071_, 2);
v___x_1158_ = l_Lean_Syntax_formatStx(v_stx_1071_, v___x_1157_, v___x_1137_);
v___x_1159_ = l_Std_Format_defWidth;
v___x_1160_ = l_Std_Format_pretty(v___x_1158_, v___x_1159_, v___x_1105_, v___x_1105_);
v___x_1161_ = lean_string_append(v___x_1156_, v___x_1160_);
lean_dec_ref(v___x_1160_);
v___x_1162_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1163_ = lean_string_append(v___x_1161_, v___x_1162_);
v___x_1164_ = l_Lean_Syntax_getKind(v_stx_1071_);
v___x_1165_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1164_, v___x_1138_);
v___x_1166_ = lean_string_append(v___x_1163_, v___x_1165_);
lean_dec_ref(v___x_1165_);
v___x_1167_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
v___x_1168_ = l_Lean_MessageData_ofFormat(v___x_1167_);
v___x_1169_ = l_Lean_throwErrorAt___redArg(v_inst_1069_, v_inst_1070_, v_stx_1071_, v___x_1168_);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; 
lean_inc(v_toPure_1082_);
lean_inc_ref(v_toFunctor_1081_);
lean_inc(v_toBind_1080_);
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_d_x3f_1153_);
v___y_1107_ = v_t_x3f_1134_;
v___y_1108_ = v___x_1135_;
v_d_x3f_1109_ = v___x_1170_;
goto v___jp_1106_;
}
}
}
else
{
lean_object* v___x_1171_; 
lean_inc(v_toPure_1082_);
lean_inc_ref(v_toFunctor_1081_);
lean_inc(v_toBind_1080_);
lean_dec(v___x_1136_);
v___x_1171_ = lean_box(0);
v___y_1107_ = v_t_x3f_1134_;
v___y_1108_ = v___x_1135_;
v_d_x3f_1109_ = v___x_1171_;
goto v___jp_1106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* v_m_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_stx_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Elab_elabTerminationHints___redArg(v_inst_1194_, v_inst_1195_, v_stx_1196_);
return v___x_1197_;
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
