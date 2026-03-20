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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_toCtorIdx___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "decreasingBy"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unexpected `decreasing_by` syntax"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "partialFixpoint"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "coinductiveFixpoint"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "inductiveFixpoint"};
static const lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorIdx(uint8_t v_x_13_){
_start:
{
switch(v_x_13_)
{
case 0:
{
lean_object* v___x_14_; 
v___x_14_ = lean_unsigned_to_nat(0u);
return v___x_14_;
}
case 1:
{
lean_object* v___x_15_; 
v___x_15_ = lean_unsigned_to_nat(1u);
return v___x_15_;
}
default: 
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(2u);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorIdx___boxed(lean_object* v_x_17_){
_start:
{
uint8_t v_x_boxed_18_; lean_object* v_res_19_; 
v_x_boxed_18_ = lean_unbox(v_x_17_);
v_res_19_ = l_Lean_Elab_PartialFixpointType_ctorIdx(v_x_boxed_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_toCtorIdx(uint8_t v_x_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Elab_PartialFixpointType_ctorIdx(v_x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_toCtorIdx___boxed(lean_object* v_x_22_){
_start:
{
uint8_t v_x_4__boxed_23_; lean_object* v_res_24_; 
v_x_4__boxed_23_ = lean_unbox(v_x_22_);
v_res_24_ = l_Lean_Elab_PartialFixpointType_toCtorIdx(v_x_4__boxed_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___redArg(lean_object* v_k_25_){
_start:
{
lean_inc(v_k_25_);
return v_k_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___redArg___boxed(lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Elab_PartialFixpointType_ctorElim___redArg(v_k_26_);
lean_dec(v_k_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim(lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, uint8_t v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_inc(v_k_32_);
return v_k_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___boxed(lean_object* v_motive_33_, lean_object* v_ctorIdx_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_k_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Lean_Elab_PartialFixpointType_ctorElim(v_motive_33_, v_ctorIdx_34_, v_t_boxed_38_, v_h_36_, v_k_37_);
lean_dec(v_k_37_);
lean_dec(v_ctorIdx_34_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(lean_object* v_partialFixpoint_40_){
_start:
{
lean_inc(v_partialFixpoint_40_);
return v_partialFixpoint_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg___boxed(lean_object* v_partialFixpoint_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(v_partialFixpoint_41_);
lean_dec(v_partialFixpoint_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_partialFixpoint_46_){
_start:
{
lean_inc(v_partialFixpoint_46_);
return v_partialFixpoint_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_partialFixpoint_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_partialFixpoint_50_);
lean_dec(v_partialFixpoint_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(lean_object* v_coinductiveFixpoint_53_){
_start:
{
lean_inc(v_coinductiveFixpoint_53_);
return v_coinductiveFixpoint_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg___boxed(lean_object* v_coinductiveFixpoint_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(v_coinductiveFixpoint_54_);
lean_dec(v_coinductiveFixpoint_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(lean_object* v_motive_56_, uint8_t v_t_57_, lean_object* v_h_58_, lean_object* v_coinductiveFixpoint_59_){
_start:
{
lean_inc(v_coinductiveFixpoint_59_);
return v_coinductiveFixpoint_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_coinductiveFixpoint_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_coinductiveFixpoint_63_);
lean_dec(v_coinductiveFixpoint_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(lean_object* v_inductiveFixpoint_66_){
_start:
{
lean_inc(v_inductiveFixpoint_66_);
return v_inductiveFixpoint_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg___boxed(lean_object* v_inductiveFixpoint_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(v_inductiveFixpoint_67_);
lean_dec(v_inductiveFixpoint_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_inductiveFixpoint_72_){
_start:
{
lean_inc(v_inductiveFixpoint_72_);
return v_inductiveFixpoint_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___boxed(lean_object* v_motive_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_inductiveFixpoint_76_){
_start:
{
uint8_t v_t_boxed_77_; lean_object* v_res_78_; 
v_t_boxed_77_ = lean_unbox(v_t_74_);
v_res_78_ = l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(v_motive_73_, v_t_boxed_77_, v_h_75_, v_inductiveFixpoint_76_);
lean_dec(v_inductiveFixpoint_76_);
return v_res_78_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedPartialFixpointType_default(void){
_start:
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedPartialFixpointType(void){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isInductiveFixpoint(uint8_t v_x_93_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_isInductiveFixpoint___boxed(lean_object* v_x_96_){
_start:
{
uint8_t v_x_21__boxed_97_; uint8_t v_res_98_; lean_object* v_r_99_; 
v_x_21__boxed_97_ = lean_unbox(v_x_96_);
v_res_98_ = l_Lean_Elab_isInductiveFixpoint(v_x_21__boxed_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isCoinductiveFixpoint(uint8_t v_x_100_){
_start:
{
if (v_x_100_ == 1)
{
uint8_t v___x_101_; 
v___x_101_ = 1;
return v___x_101_;
}
else
{
uint8_t v___x_102_; 
v___x_102_ = 0;
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isCoinductiveFixpoint___boxed(lean_object* v_x_103_){
_start:
{
uint8_t v_x_21__boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_x_21__boxed_104_ = lean_unbox(v_x_103_);
v_res_105_ = l_Lean_Elab_isCoinductiveFixpoint(v_x_21__boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isPartialFixpoint(uint8_t v_x_107_){
_start:
{
if (v_x_107_ == 0)
{
uint8_t v___x_108_; 
v___x_108_ = 1;
return v___x_108_;
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isPartialFixpoint___boxed(lean_object* v_x_110_){
_start:
{
uint8_t v_x_21__boxed_111_; uint8_t v_res_112_; lean_object* v_r_113_; 
v_x_21__boxed_111_ = lean_unbox(v_x_110_);
v_res_112_ = l_Lean_Elab_isPartialFixpoint(v_x_21__boxed_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isLatticeTheoretic(uint8_t v_p_114_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = l_Lean_Elab_isInductiveFixpoint(v_p_114_);
if (v___x_115_ == 0)
{
uint8_t v___x_116_; 
v___x_116_ = l_Lean_Elab_isCoinductiveFixpoint(v_p_114_);
return v___x_116_;
}
else
{
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isLatticeTheoretic___boxed(lean_object* v_p_117_){
_start:
{
uint8_t v_p_boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v_p_boxed_118_ = lean_unbox(v_p_117_);
v_res_119_ = l_Lean_Elab_isLatticeTheoretic(v_p_boxed_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_122_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
lean_ctor_set(v___x_127_, 2, v___x_126_);
lean_ctor_set(v___x_127_, 3, v___x_125_);
lean_ctor_set(v___x_127_, 4, v___x_125_);
lean_ctor_set(v___x_127_, 5, v___x_125_);
lean_ctor_set(v___x_127_, 6, v___x_125_);
lean_ctor_set(v___x_127_, 7, v___x_125_);
lean_ctor_set(v___x_127_, 8, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(32u);
v___x_129_ = lean_mk_empty_array_with_capacity(v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_131_ = ((size_t)5ULL);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_unsigned_to_nat(32u);
v___x_134_ = lean_mk_empty_array_with_capacity(v___x_133_);
v___x_135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3);
v___x_136_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_132_);
lean_ctor_set(v___x_136_, 3, v___x_132_);
lean_ctor_set_usize(v___x_136_, 4, v___x_131_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = lean_box(1);
v___x_138_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4);
v___x_139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
v___x_140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_137_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(lean_object* v_msgData_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; lean_object* v_env_146_; lean_object* v_options_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_145_ = lean_st_ref_get(v___y_143_);
v_env_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc_ref(v_env_146_);
lean_dec(v___x_145_);
v_options_147_ = lean_ctor_get(v___y_142_, 2);
v___x_148_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2);
v___x_149_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_147_);
v___x_150_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_150_, 0, v_env_146_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
lean_ctor_set(v___x_150_, 2, v___x_149_);
lean_ctor_set(v___x_150_, 3, v_options_147_);
v___x_151_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_msgData_141_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v_msgData_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_157_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(uint8_t v___y_166_, uint8_t v_suppressElabErrors_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_168_) == 1)
{
lean_object* v_pre_169_; 
v_pre_169_ = lean_ctor_get(v_x_168_, 0);
switch(lean_obj_tag(v_pre_169_))
{
case 1:
{
lean_object* v_pre_170_; 
v_pre_170_ = lean_ctor_get(v_pre_169_, 0);
switch(lean_obj_tag(v_pre_170_))
{
case 0:
{
lean_object* v_str_171_; lean_object* v_str_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_str_171_ = lean_ctor_get(v_x_168_, 1);
v_str_172_ = lean_ctor_get(v_pre_169_, 1);
v___x_173_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0));
v___x_174_ = lean_string_dec_eq(v_str_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1));
v___x_176_ = lean_string_dec_eq(v_str_172_, v___x_175_);
if (v___x_176_ == 0)
{
return v___y_166_;
}
else
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2));
v___x_178_ = lean_string_dec_eq(v_str_171_, v___x_177_);
if (v___x_178_ == 0)
{
return v___y_166_;
}
else
{
return v_suppressElabErrors_167_;
}
}
}
else
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3));
v___x_180_ = lean_string_dec_eq(v_str_171_, v___x_179_);
if (v___x_180_ == 0)
{
return v___y_166_;
}
else
{
return v_suppressElabErrors_167_;
}
}
}
case 1:
{
lean_object* v_pre_181_; 
v_pre_181_ = lean_ctor_get(v_pre_170_, 0);
if (lean_obj_tag(v_pre_181_) == 0)
{
lean_object* v_str_182_; lean_object* v_str_183_; lean_object* v_str_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_str_182_ = lean_ctor_get(v_x_168_, 1);
v_str_183_ = lean_ctor_get(v_pre_169_, 1);
v_str_184_ = lean_ctor_get(v_pre_170_, 1);
v___x_185_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4));
v___x_186_ = lean_string_dec_eq(v_str_184_, v___x_185_);
if (v___x_186_ == 0)
{
return v___y_166_;
}
else
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5));
v___x_188_ = lean_string_dec_eq(v_str_183_, v___x_187_);
if (v___x_188_ == 0)
{
return v___y_166_;
}
else
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6));
v___x_190_ = lean_string_dec_eq(v_str_182_, v___x_189_);
if (v___x_190_ == 0)
{
return v___y_166_;
}
else
{
return v_suppressElabErrors_167_;
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
lean_object* v_str_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_str_191_ = lean_ctor_get(v_x_168_, 1);
v___x_192_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7));
v___x_193_ = lean_string_dec_eq(v_str_191_, v___x_192_);
if (v___x_193_ == 0)
{
return v___y_166_;
}
else
{
return v_suppressElabErrors_167_;
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
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed(lean_object* v___y_194_, lean_object* v_suppressElabErrors_195_, lean_object* v_x_196_){
_start:
{
uint8_t v___y_3233__boxed_197_; uint8_t v_suppressElabErrors_boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v___y_3233__boxed_197_ = lean_unbox(v___y_194_);
v_suppressElabErrors_boxed_198_ = lean_unbox(v_suppressElabErrors_195_);
v_res_199_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v___y_3233__boxed_197_, v_suppressElabErrors_boxed_198_, v_x_196_);
lean_dec(v_x_196_);
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
lean_dec_ref(v___x_206_);
if (lean_obj_tag(v_val_208_) == 1)
{
uint8_t v_v_209_; 
v_v_209_ = lean_ctor_get_uint8(v_val_208_, 0);
lean_dec_ref(v_val_208_);
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
lean_object* v___y_224_; lean_object* v___y_225_; uint8_t v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; uint8_t v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_260_; uint8_t v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; uint8_t v___y_264_; lean_object* v___y_265_; uint8_t v___y_266_; lean_object* v___y_267_; lean_object* v___y_285_; uint8_t v___y_286_; lean_object* v___y_287_; uint8_t v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; uint8_t v___y_291_; lean_object* v___y_292_; lean_object* v___y_296_; uint8_t v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; uint8_t v___y_301_; uint8_t v___y_302_; uint8_t v___x_307_; lean_object* v___y_309_; uint8_t v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; uint8_t v___y_314_; uint8_t v___y_315_; uint8_t v___y_317_; uint8_t v___x_332_; 
v___x_307_ = 2;
v___x_332_ = l_Lean_instBEqMessageSeverity_beq(v_severity_218_, v___x_307_);
if (v___x_332_ == 0)
{
v___y_317_ = v___x_332_;
goto v___jp_316_;
}
else
{
uint8_t v___x_333_; 
lean_inc_ref(v_msgData_217_);
v___x_333_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_217_);
v___y_317_ = v___x_333_;
goto v___jp_316_;
}
v___jp_223_:
{
lean_object* v___x_233_; lean_object* v_currNamespace_234_; lean_object* v_openDecls_235_; lean_object* v_env_236_; lean_object* v_nextMacroScope_237_; lean_object* v_ngen_238_; lean_object* v_auxDeclNGen_239_; lean_object* v_traceState_240_; lean_object* v_cache_241_; lean_object* v_messages_242_; lean_object* v_infoState_243_; lean_object* v_snapshotTasks_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_258_; 
v___x_233_ = lean_st_ref_take(v___y_232_);
v_currNamespace_234_ = lean_ctor_get(v___y_231_, 6);
lean_inc(v_currNamespace_234_);
v_openDecls_235_ = lean_ctor_get(v___y_231_, 7);
lean_inc(v_openDecls_235_);
lean_dec_ref(v___y_231_);
v_env_236_ = lean_ctor_get(v___x_233_, 0);
v_nextMacroScope_237_ = lean_ctor_get(v___x_233_, 1);
v_ngen_238_ = lean_ctor_get(v___x_233_, 2);
v_auxDeclNGen_239_ = lean_ctor_get(v___x_233_, 3);
v_traceState_240_ = lean_ctor_get(v___x_233_, 4);
v_cache_241_ = lean_ctor_get(v___x_233_, 5);
v_messages_242_ = lean_ctor_get(v___x_233_, 6);
v_infoState_243_ = lean_ctor_get(v___x_233_, 7);
v_snapshotTasks_244_ = lean_ctor_get(v___x_233_, 8);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_258_ == 0)
{
v___x_246_ = v___x_233_;
v_isShared_247_ = v_isSharedCheck_258_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_snapshotTasks_244_);
lean_inc(v_infoState_243_);
lean_inc(v_messages_242_);
lean_inc(v_cache_241_);
lean_inc(v_traceState_240_);
lean_inc(v_auxDeclNGen_239_);
lean_inc(v_ngen_238_);
lean_inc(v_nextMacroScope_237_);
lean_inc(v_env_236_);
lean_dec(v___x_233_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_258_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_currNamespace_234_);
lean_ctor_set(v___x_248_, 1, v_openDecls_235_);
v___x_249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___y_228_);
v___x_250_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_250_, 0, v___y_225_);
lean_ctor_set(v___x_250_, 1, v___y_227_);
lean_ctor_set(v___x_250_, 2, v___y_224_);
lean_ctor_set(v___x_250_, 3, v___y_230_);
lean_ctor_set(v___x_250_, 4, v___x_249_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*5, v___y_229_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*5 + 1, v___y_226_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*5 + 2, v_isSilent_219_);
v___x_251_ = l_Lean_MessageLog_add(v___x_250_, v_messages_242_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 6, v___x_251_);
v___x_253_ = v___x_246_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_env_236_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_nextMacroScope_237_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_ngen_238_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v_auxDeclNGen_239_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v_traceState_240_);
lean_ctor_set(v_reuseFailAlloc_257_, 5, v_cache_241_);
lean_ctor_set(v_reuseFailAlloc_257_, 6, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_257_, 7, v_infoState_243_);
lean_ctor_set(v_reuseFailAlloc_257_, 8, v_snapshotTasks_244_);
v___x_253_ = v_reuseFailAlloc_257_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_st_ref_set(v___y_232_, v___x_253_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
v___jp_259_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_283_; 
v___x_268_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_217_);
v___x_269_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v___x_268_, v___y_220_, v___y_221_);
v_a_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_283_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_283_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_283_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_inc_ref(v___y_265_);
v___x_274_ = l_Lean_FileMap_toPosition(v___y_265_, v___y_262_);
lean_dec(v___y_262_);
v___x_275_ = l_Lean_FileMap_toPosition(v___y_265_, v___y_267_);
lean_dec(v___y_267_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
v___x_277_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0));
if (v___y_261_ == 0)
{
lean_del_object(v___x_272_);
lean_dec_ref(v___y_260_);
v___y_224_ = v___x_276_;
v___y_225_ = v___y_263_;
v___y_226_ = v___y_264_;
v___y_227_ = v___x_274_;
v___y_228_ = v_a_270_;
v___y_229_ = v___y_266_;
v___y_230_ = v___x_277_;
v___y_231_ = v___y_220_;
v___y_232_ = v___y_221_;
goto v___jp_223_;
}
else
{
uint8_t v___x_278_; 
lean_inc(v_a_270_);
v___x_278_ = l_Lean_MessageData_hasTag(v___y_260_, v_a_270_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_281_; 
lean_dec_ref(v___x_276_);
lean_dec_ref(v___x_274_);
lean_dec(v_a_270_);
lean_dec_ref(v___y_263_);
lean_dec_ref(v___y_220_);
v___x_279_ = lean_box(0);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_279_);
v___x_281_ = v___x_272_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
else
{
lean_del_object(v___x_272_);
v___y_224_ = v___x_276_;
v___y_225_ = v___y_263_;
v___y_226_ = v___y_264_;
v___y_227_ = v___x_274_;
v___y_228_ = v_a_270_;
v___y_229_ = v___y_266_;
v___y_230_ = v___x_277_;
v___y_231_ = v___y_220_;
v___y_232_ = v___y_221_;
goto v___jp_223_;
}
}
}
}
v___jp_284_:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Syntax_getTailPos_x3f(v___y_289_, v___y_291_);
lean_dec(v___y_289_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_inc(v___y_292_);
v___y_260_ = v___y_285_;
v___y_261_ = v___y_286_;
v___y_262_ = v___y_292_;
v___y_263_ = v___y_287_;
v___y_264_ = v___y_288_;
v___y_265_ = v___y_290_;
v___y_266_ = v___y_291_;
v___y_267_ = v___y_292_;
goto v___jp_259_;
}
else
{
lean_object* v_val_294_; 
v_val_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_val_294_);
lean_dec_ref(v___x_293_);
v___y_260_ = v___y_285_;
v___y_261_ = v___y_286_;
v___y_262_ = v___y_292_;
v___y_263_ = v___y_287_;
v___y_264_ = v___y_288_;
v___y_265_ = v___y_290_;
v___y_266_ = v___y_291_;
v___y_267_ = v_val_294_;
goto v___jp_259_;
}
}
v___jp_295_:
{
lean_object* v_ref_303_; lean_object* v___x_304_; 
v_ref_303_ = l_Lean_replaceRef(v_ref_216_, v___y_300_);
lean_dec(v___y_300_);
v___x_304_ = l_Lean_Syntax_getPos_x3f(v_ref_303_, v___y_301_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_unsigned_to_nat(0u);
v___y_285_ = v___y_296_;
v___y_286_ = v___y_297_;
v___y_287_ = v___y_298_;
v___y_288_ = v___y_302_;
v___y_289_ = v_ref_303_;
v___y_290_ = v___y_299_;
v___y_291_ = v___y_301_;
v___y_292_ = v___x_305_;
goto v___jp_284_;
}
else
{
lean_object* v_val_306_; 
v_val_306_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_val_306_);
lean_dec_ref(v___x_304_);
v___y_285_ = v___y_296_;
v___y_286_ = v___y_297_;
v___y_287_ = v___y_298_;
v___y_288_ = v___y_302_;
v___y_289_ = v_ref_303_;
v___y_290_ = v___y_299_;
v___y_291_ = v___y_301_;
v___y_292_ = v_val_306_;
goto v___jp_284_;
}
}
v___jp_308_:
{
if (v___y_315_ == 0)
{
v___y_296_ = v___y_309_;
v___y_297_ = v___y_310_;
v___y_298_ = v___y_311_;
v___y_299_ = v___y_313_;
v___y_300_ = v___y_312_;
v___y_301_ = v___y_314_;
v___y_302_ = v_severity_218_;
goto v___jp_295_;
}
else
{
v___y_296_ = v___y_309_;
v___y_297_ = v___y_310_;
v___y_298_ = v___y_311_;
v___y_299_ = v___y_313_;
v___y_300_ = v___y_312_;
v___y_301_ = v___y_314_;
v___y_302_ = v___x_307_;
goto v___jp_295_;
}
}
v___jp_316_:
{
if (v___y_317_ == 0)
{
lean_object* v_fileName_318_; lean_object* v_fileMap_319_; lean_object* v_options_320_; lean_object* v_ref_321_; uint8_t v_suppressElabErrors_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___f_325_; uint8_t v___x_326_; uint8_t v___x_327_; 
v_fileName_318_ = lean_ctor_get(v___y_220_, 0);
v_fileMap_319_ = lean_ctor_get(v___y_220_, 1);
v_options_320_ = lean_ctor_get(v___y_220_, 2);
v_ref_321_ = lean_ctor_get(v___y_220_, 5);
v_suppressElabErrors_322_ = lean_ctor_get_uint8(v___y_220_, sizeof(void*)*14 + 1);
v___x_323_ = lean_box(v___y_317_);
v___x_324_ = lean_box(v_suppressElabErrors_322_);
v___f_325_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_325_, 0, v___x_323_);
lean_closure_set(v___f_325_, 1, v___x_324_);
v___x_326_ = 1;
v___x_327_ = l_Lean_instBEqMessageSeverity_beq(v_severity_218_, v___x_326_);
if (v___x_327_ == 0)
{
lean_inc_ref(v_fileMap_319_);
lean_inc(v_ref_321_);
lean_inc_ref(v_fileName_318_);
v___y_309_ = v___f_325_;
v___y_310_ = v_suppressElabErrors_322_;
v___y_311_ = v_fileName_318_;
v___y_312_ = v_ref_321_;
v___y_313_ = v_fileMap_319_;
v___y_314_ = v___y_317_;
v___y_315_ = v___x_327_;
goto v___jp_308_;
}
else
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = l_Lean_warningAsError;
v___x_329_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_options_320_, v___x_328_);
lean_inc_ref(v_fileMap_319_);
lean_inc(v_ref_321_);
lean_inc_ref(v_fileName_318_);
v___y_309_ = v___f_325_;
v___y_310_ = v_suppressElabErrors_322_;
v___y_311_ = v_fileName_318_;
v___y_312_ = v_ref_321_;
v___y_313_ = v_fileMap_319_;
v___y_314_ = v___y_317_;
v___y_315_ = v___x_329_;
goto v___jp_308_;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec_ref(v___y_220_);
lean_dec_ref(v_msgData_217_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___boxed(lean_object* v_ref_334_, lean_object* v_msgData_335_, lean_object* v_severity_336_, lean_object* v_isSilent_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
uint8_t v_severity_boxed_341_; uint8_t v_isSilent_boxed_342_; lean_object* v_res_343_; 
v_severity_boxed_341_ = lean_unbox(v_severity_336_);
v_isSilent_boxed_342_ = lean_unbox(v_isSilent_337_);
v_res_343_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_334_, v_msgData_335_, v_severity_boxed_341_, v_isSilent_boxed_342_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec(v_ref_334_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(lean_object* v_ref_344_, lean_object* v_msgData_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
uint8_t v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; 
v___x_349_ = 1;
v___x_350_ = 0;
v___x_351_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_344_, v_msgData_345_, v___x_349_, v___x_350_, v___y_346_, v___y_347_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(lean_object* v_ref_352_, lean_object* v_msgData_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_352_, v_msgData_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec(v_ref_352_);
return v_res_357_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__0));
v___x_360_ = l_Lean_stringToMessageData(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__2));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__4));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__6));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__8));
v___x_372_ = l_Lean_stringToMessageData(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__10));
v___x_375_ = l_Lean_stringToMessageData(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__12));
v___x_378_ = l_Lean_stringToMessageData(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone(lean_object* v_hints_379_, lean_object* v_reason_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_ref_384_; lean_object* v_terminationBy_x3f_x3f_385_; lean_object* v_terminationBy_x3f_386_; lean_object* v_partialFixpoint_x3f_387_; lean_object* v_decreasingBy_x3f_388_; lean_object* v___y_390_; lean_object* v___y_391_; 
v_ref_384_ = lean_ctor_get(v_hints_379_, 0);
lean_inc(v_ref_384_);
v_terminationBy_x3f_x3f_385_ = lean_ctor_get(v_hints_379_, 1);
lean_inc(v_terminationBy_x3f_x3f_385_);
v_terminationBy_x3f_386_ = lean_ctor_get(v_hints_379_, 2);
lean_inc(v_terminationBy_x3f_386_);
v_partialFixpoint_x3f_387_ = lean_ctor_get(v_hints_379_, 3);
lean_inc(v_partialFixpoint_x3f_387_);
v_decreasingBy_x3f_388_ = lean_ctor_get(v_hints_379_, 4);
lean_inc(v_decreasingBy_x3f_388_);
lean_dec_ref(v_hints_379_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_385_) == 0)
{
if (lean_obj_tag(v_terminationBy_x3f_386_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_388_) == 0)
{
lean_dec(v_ref_384_);
if (lean_obj_tag(v_partialFixpoint_x3f_387_) == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref(v_a_381_);
lean_dec_ref(v_reason_380_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
else
{
lean_object* v_val_398_; uint8_t v_fixpointType_399_; 
v_val_398_ = lean_ctor_get(v_partialFixpoint_x3f_387_, 0);
lean_inc(v_val_398_);
lean_dec_ref(v_partialFixpoint_x3f_387_);
v_fixpointType_399_ = lean_ctor_get_uint8(v_val_398_, sizeof(void*)*2);
switch(v_fixpointType_399_)
{
case 0:
{
lean_object* v_ref_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_ref_400_ = lean_ctor_get(v_val_398_, 0);
lean_inc(v_ref_400_);
lean_dec(v_val_398_);
v___x_401_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__3, &l_Lean_Elab_TerminationHints_ensureNone___closed__3_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3);
v___x_402_ = l_Lean_stringToMessageData(v_reason_380_);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_400_, v___x_403_, v_a_381_, v_a_382_);
lean_dec(v_ref_400_);
return v___x_404_;
}
case 1:
{
lean_object* v_ref_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_ref_405_ = lean_ctor_get(v_val_398_, 0);
lean_inc(v_ref_405_);
lean_dec(v_val_398_);
v___x_406_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__5, &l_Lean_Elab_TerminationHints_ensureNone___closed__5_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5);
v___x_407_ = l_Lean_stringToMessageData(v_reason_380_);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_405_, v___x_408_, v_a_381_, v_a_382_);
lean_dec(v_ref_405_);
return v___x_409_;
}
default: 
{
lean_object* v_ref_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_ref_410_ = lean_ctor_get(v_val_398_, 0);
lean_inc(v_ref_410_);
lean_dec(v_val_398_);
v___x_411_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__7, &l_Lean_Elab_TerminationHints_ensureNone___closed__7_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7);
v___x_412_ = l_Lean_stringToMessageData(v_reason_380_);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_410_, v___x_413_, v_a_381_, v_a_382_);
lean_dec(v_ref_410_);
return v___x_414_;
}
}
}
}
else
{
if (lean_obj_tag(v_partialFixpoint_x3f_387_) == 0)
{
lean_object* v_val_415_; lean_object* v_ref_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_ref_384_);
v_val_415_ = lean_ctor_get(v_decreasingBy_x3f_388_, 0);
lean_inc(v_val_415_);
lean_dec_ref(v_decreasingBy_x3f_388_);
v_ref_416_ = lean_ctor_get(v_val_415_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_val_415_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v_val_415_, 1);
lean_dec(v_unused_427_);
v___x_418_ = v_val_415_;
v_isShared_419_ = v_isSharedCheck_426_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_ref_416_);
lean_dec(v_val_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_426_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_420_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__9, &l_Lean_Elab_TerminationHints_ensureNone___closed__9_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9);
v___x_421_ = l_Lean_stringToMessageData(v_reason_380_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 7);
lean_ctor_set(v___x_418_, 1, v___x_421_);
lean_ctor_set(v___x_418_, 0, v___x_420_);
v___x_423_ = v___x_418_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_425_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_416_, v___x_423_, v_a_381_, v_a_382_);
lean_dec(v_ref_416_);
return v___x_424_;
}
}
}
else
{
lean_dec_ref(v_decreasingBy_x3f_388_);
lean_dec(v_partialFixpoint_x3f_387_);
v___y_390_ = v_a_381_;
v___y_391_ = v_a_382_;
goto v___jp_389_;
}
}
}
else
{
if (lean_obj_tag(v_decreasingBy_x3f_388_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_387_) == 0)
{
lean_object* v_val_428_; lean_object* v_ref_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec(v_ref_384_);
v_val_428_ = lean_ctor_get(v_terminationBy_x3f_386_, 0);
lean_inc(v_val_428_);
lean_dec_ref(v_terminationBy_x3f_386_);
v_ref_429_ = lean_ctor_get(v_val_428_, 0);
lean_inc(v_ref_429_);
lean_dec(v_val_428_);
v___x_430_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__11, &l_Lean_Elab_TerminationHints_ensureNone___closed__11_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11);
v___x_431_ = l_Lean_stringToMessageData(v_reason_380_);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_429_, v___x_432_, v_a_381_, v_a_382_);
lean_dec(v_ref_429_);
return v___x_433_;
}
else
{
lean_dec_ref(v_terminationBy_x3f_386_);
lean_dec(v_partialFixpoint_x3f_387_);
v___y_390_ = v_a_381_;
v___y_391_ = v_a_382_;
goto v___jp_389_;
}
}
else
{
lean_dec_ref(v_terminationBy_x3f_386_);
lean_dec(v_decreasingBy_x3f_388_);
lean_dec(v_partialFixpoint_x3f_387_);
v___y_390_ = v_a_381_;
v___y_391_ = v_a_382_;
goto v___jp_389_;
}
}
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_386_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_388_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_387_) == 0)
{
lean_object* v_val_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v_ref_384_);
v_val_434_ = lean_ctor_get(v_terminationBy_x3f_x3f_385_, 0);
lean_inc(v_val_434_);
lean_dec_ref(v_terminationBy_x3f_x3f_385_);
v___x_435_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__13, &l_Lean_Elab_TerminationHints_ensureNone___closed__13_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13);
v___x_436_ = l_Lean_stringToMessageData(v_reason_380_);
v___x_437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_435_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_val_434_, v___x_437_, v_a_381_, v_a_382_);
lean_dec(v_val_434_);
return v___x_438_;
}
else
{
lean_dec_ref(v_terminationBy_x3f_x3f_385_);
lean_dec(v_partialFixpoint_x3f_387_);
v___y_390_ = v_a_381_;
v___y_391_ = v_a_382_;
goto v___jp_389_;
}
}
else
{
lean_dec_ref(v_terminationBy_x3f_x3f_385_);
lean_dec(v_decreasingBy_x3f_388_);
lean_dec(v_partialFixpoint_x3f_387_);
v___y_390_ = v_a_381_;
v___y_391_ = v_a_382_;
goto v___jp_389_;
}
}
else
{
lean_dec_ref(v_terminationBy_x3f_x3f_385_);
lean_dec(v_decreasingBy_x3f_388_);
lean_dec(v_partialFixpoint_x3f_387_);
lean_dec(v_terminationBy_x3f_386_);
v___y_390_ = v_a_381_;
v___y_391_ = v_a_382_;
goto v___jp_389_;
}
}
v___jp_389_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__1, &l_Lean_Elab_TerminationHints_ensureNone___closed__1_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1);
v___x_393_ = l_Lean_stringToMessageData(v_reason_380_);
v___x_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_384_, v___x_394_, v___y_390_, v___y_391_);
lean_dec(v_ref_384_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone___boxed(lean_object* v_hints_439_, lean_object* v_reason_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Elab_TerminationHints_ensureNone(v_hints_439_, v_reason_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
return v_res_444_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_TerminationHints_isNotNone(lean_object* v_hints_445_){
_start:
{
lean_object* v_terminationBy_x3f_x3f_446_; 
v_terminationBy_x3f_x3f_446_ = lean_ctor_get(v_hints_445_, 1);
if (lean_obj_tag(v_terminationBy_x3f_x3f_446_) == 0)
{
lean_object* v_terminationBy_x3f_447_; 
v_terminationBy_x3f_447_ = lean_ctor_get(v_hints_445_, 2);
if (lean_obj_tag(v_terminationBy_x3f_447_) == 0)
{
lean_object* v_decreasingBy_x3f_448_; 
v_decreasingBy_x3f_448_ = lean_ctor_get(v_hints_445_, 4);
if (lean_obj_tag(v_decreasingBy_x3f_448_) == 0)
{
lean_object* v_partialFixpoint_x3f_449_; 
v_partialFixpoint_x3f_449_ = lean_ctor_get(v_hints_445_, 3);
if (lean_obj_tag(v_partialFixpoint_x3f_449_) == 0)
{
uint8_t v___x_450_; 
v___x_450_ = 0;
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = 1;
return v___x_451_;
}
}
else
{
uint8_t v___x_452_; 
v___x_452_ = 1;
return v___x_452_;
}
}
else
{
uint8_t v___x_453_; 
v___x_453_ = 1;
return v___x_453_;
}
}
else
{
uint8_t v___x_454_; 
v___x_454_ = 1;
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_isNotNone___boxed(lean_object* v_hints_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_Lean_Elab_TerminationHints_isNotNone(v_hints_455_);
lean_dec_ref(v_hints_455_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object* v_headerParams_458_, lean_object* v_hints_459_, lean_object* v_value_460_){
_start:
{
lean_object* v_ref_461_; lean_object* v_terminationBy_x3f_x3f_462_; lean_object* v_terminationBy_x3f_463_; lean_object* v_partialFixpoint_x3f_464_; lean_object* v_decreasingBy_x3f_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
v_ref_461_ = lean_ctor_get(v_hints_459_, 0);
v_terminationBy_x3f_x3f_462_ = lean_ctor_get(v_hints_459_, 1);
v_terminationBy_x3f_463_ = lean_ctor_get(v_hints_459_, 2);
v_partialFixpoint_x3f_464_ = lean_ctor_get(v_hints_459_, 3);
v_decreasingBy_x3f_465_ = lean_ctor_get(v_hints_459_, 4);
v_isSharedCheck_474_ = !lean_is_exclusive(v_hints_459_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v_hints_459_, 5);
lean_dec(v_unused_475_);
v___x_467_ = v_hints_459_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_decreasingBy_x3f_465_);
lean_inc(v_partialFixpoint_x3f_464_);
lean_inc(v_terminationBy_x3f_463_);
lean_inc(v_terminationBy_x3f_x3f_462_);
lean_inc(v_ref_461_);
lean_dec(v_hints_459_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = l_Lean_Expr_getNumHeadLambdas(v_value_460_);
v___x_470_ = lean_nat_sub(v___x_469_, v_headerParams_458_);
lean_dec(v___x_469_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 5, v___x_470_);
v___x_472_ = v___x_467_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_ref_461_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_terminationBy_x3f_x3f_462_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_terminationBy_x3f_463_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_partialFixpoint_x3f_464_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v_decreasingBy_x3f_465_);
lean_ctor_set(v_reuseFailAlloc_473_, 5, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(lean_object* v_headerParams_476_, lean_object* v_hints_477_, lean_object* v_value_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v_headerParams_476_, v_hints_477_, v_value_478_);
lean_dec_ref(v_value_478_);
lean_dec(v_headerParams_476_);
return v_res_479_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3));
v___x_487_ = l_Lean_MessageData_ofFormat(v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(lean_object* v_a_488_){
_start:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_dec_eq(v_a_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = l_Nat_reprFast(v_a_488_);
v___x_492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
v___x_493_ = l_Lean_MessageData_ofFormat(v___x_492_);
v___x_494_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1);
v___x_495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; 
lean_dec(v_a_488_);
v___x_496_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(lean_object* v_msgData_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; lean_object* v_env_504_; lean_object* v___x_505_; lean_object* v_mctx_506_; lean_object* v_lctx_507_; lean_object* v_options_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_503_ = lean_st_ref_get(v___y_501_);
v_env_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc_ref(v_env_504_);
lean_dec(v___x_503_);
v___x_505_ = lean_st_ref_get(v___y_499_);
v_mctx_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc_ref(v_mctx_506_);
lean_dec(v___x_505_);
v_lctx_507_ = lean_ctor_get(v___y_498_, 2);
v_options_508_ = lean_ctor_get(v___y_500_, 2);
lean_inc_ref(v_options_508_);
lean_inc_ref(v_lctx_507_);
v___x_509_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_509_, 0, v_env_504_);
lean_ctor_set(v___x_509_, 1, v_mctx_506_);
lean_ctor_set(v___x_509_, 2, v_lctx_507_);
lean_ctor_set(v___x_509_, 3, v_options_508_);
v___x_510_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_msgData_497_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(lean_object* v_msg_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_ref_525_; lean_object* v___x_526_; lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_535_; 
v_ref_525_ = lean_ctor_get(v___y_522_, 5);
v___x_526_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msg_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_535_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
lean_inc(v_ref_525_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_ref_525_);
lean_ctor_set(v___x_531_, 1, v_a_527_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 1);
lean_ctor_set(v___x_529_, 0, v___x_531_);
v___x_533_ = v___x_529_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_msg_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object* v_ref_543_, lean_object* v_msg_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_fileName_550_; lean_object* v_fileMap_551_; lean_object* v_options_552_; lean_object* v_currRecDepth_553_; lean_object* v_maxRecDepth_554_; lean_object* v_ref_555_; lean_object* v_currNamespace_556_; lean_object* v_openDecls_557_; lean_object* v_initHeartbeats_558_; lean_object* v_maxHeartbeats_559_; lean_object* v_quotContext_560_; lean_object* v_currMacroScope_561_; uint8_t v_diag_562_; lean_object* v_cancelTk_x3f_563_; uint8_t v_suppressElabErrors_564_; lean_object* v_inheritedTraceOptions_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_574_; 
v_fileName_550_ = lean_ctor_get(v___y_547_, 0);
v_fileMap_551_ = lean_ctor_get(v___y_547_, 1);
v_options_552_ = lean_ctor_get(v___y_547_, 2);
v_currRecDepth_553_ = lean_ctor_get(v___y_547_, 3);
v_maxRecDepth_554_ = lean_ctor_get(v___y_547_, 4);
v_ref_555_ = lean_ctor_get(v___y_547_, 5);
v_currNamespace_556_ = lean_ctor_get(v___y_547_, 6);
v_openDecls_557_ = lean_ctor_get(v___y_547_, 7);
v_initHeartbeats_558_ = lean_ctor_get(v___y_547_, 8);
v_maxHeartbeats_559_ = lean_ctor_get(v___y_547_, 9);
v_quotContext_560_ = lean_ctor_get(v___y_547_, 10);
v_currMacroScope_561_ = lean_ctor_get(v___y_547_, 11);
v_diag_562_ = lean_ctor_get_uint8(v___y_547_, sizeof(void*)*14);
v_cancelTk_x3f_563_ = lean_ctor_get(v___y_547_, 12);
v_suppressElabErrors_564_ = lean_ctor_get_uint8(v___y_547_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_565_ = lean_ctor_get(v___y_547_, 13);
v_isSharedCheck_574_ = !lean_is_exclusive(v___y_547_);
if (v_isSharedCheck_574_ == 0)
{
v___x_567_ = v___y_547_;
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_inheritedTraceOptions_565_);
lean_inc(v_cancelTk_x3f_563_);
lean_inc(v_currMacroScope_561_);
lean_inc(v_quotContext_560_);
lean_inc(v_maxHeartbeats_559_);
lean_inc(v_initHeartbeats_558_);
lean_inc(v_openDecls_557_);
lean_inc(v_currNamespace_556_);
lean_inc(v_ref_555_);
lean_inc(v_maxRecDepth_554_);
lean_inc(v_currRecDepth_553_);
lean_inc(v_options_552_);
lean_inc(v_fileMap_551_);
lean_inc(v_fileName_550_);
lean_dec(v___y_547_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_ref_569_; lean_object* v___x_571_; 
v_ref_569_ = l_Lean_replaceRef(v_ref_543_, v_ref_555_);
lean_dec(v_ref_555_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 5, v_ref_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_fileName_550_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_fileMap_551_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_options_552_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_currRecDepth_553_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v_maxRecDepth_554_);
lean_ctor_set(v_reuseFailAlloc_573_, 5, v_ref_569_);
lean_ctor_set(v_reuseFailAlloc_573_, 6, v_currNamespace_556_);
lean_ctor_set(v_reuseFailAlloc_573_, 7, v_openDecls_557_);
lean_ctor_set(v_reuseFailAlloc_573_, 8, v_initHeartbeats_558_);
lean_ctor_set(v_reuseFailAlloc_573_, 9, v_maxHeartbeats_559_);
lean_ctor_set(v_reuseFailAlloc_573_, 10, v_quotContext_560_);
lean_ctor_set(v_reuseFailAlloc_573_, 11, v_currMacroScope_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 12, v_cancelTk_x3f_563_);
lean_ctor_set(v_reuseFailAlloc_573_, 13, v_inheritedTraceOptions_565_);
lean_ctor_set_uint8(v_reuseFailAlloc_573_, sizeof(void*)*14, v_diag_562_);
lean_ctor_set_uint8(v_reuseFailAlloc_573_, sizeof(void*)*14 + 1, v_suppressElabErrors_564_);
v___x_571_ = v_reuseFailAlloc_573_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_544_, v___y_545_, v___y_546_, v___x_571_, v___y_548_);
lean_dec_ref(v___x_571_);
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object* v_ref_575_, lean_object* v_msg_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_575_, v_msg_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v_ref_575_);
return v_res_582_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__1(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__0));
v___x_585_ = l_Lean_stringToMessageData(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__3(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__2));
v___x_588_ = l_Lean_stringToMessageData(v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__5(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__4));
v___x_591_ = l_Lean_stringToMessageData(v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__9(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__8));
v___x_597_ = l_Lean_stringToMessageData(v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__12(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__11));
v___x_602_ = l_Lean_MessageData_ofFormat(v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object* v_funName_603_, lean_object* v_extraParams_604_, lean_object* v_tb_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
uint8_t v_synthetic_611_; 
v_synthetic_611_ = lean_ctor_get_uint8(v_tb_605_, sizeof(void*)*3 + 1);
if (v_synthetic_611_ == 0)
{
lean_object* v_ref_612_; lean_object* v_vars_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_ref_612_ = lean_ctor_get(v_tb_605_, 0);
v_vars_613_ = lean_ctor_get(v_tb_605_, 1);
v___x_614_ = lean_array_get_size(v_vars_613_);
v___x_615_ = lean_nat_dec_lt(v_extraParams_604_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
lean_dec_ref(v_a_608_);
lean_dec(v_extraParams_604_);
lean_dec(v_funName_603_);
v___x_616_ = lean_box(0);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v_msg_628_; lean_object* v___x_629_; lean_object* v_ident_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_618_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_614_);
v___x_619_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__1, &l_Lean_Elab_TerminationBy_checkVars___closed__1_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__1);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
lean_inc(v_funName_603_);
v___x_621_ = l_Lean_MessageData_ofName(v_funName_603_);
v___x_622_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__3, &l_Lean_Elab_TerminationBy_checkVars___closed__3_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__3);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_604_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__5, &l_Lean_Elab_TerminationBy_checkVars___closed__5_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__5);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v_msg_628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_628_, 0, v___x_620_);
lean_ctor_set(v_msg_628_, 1, v___x_627_);
v___x_629_ = lean_unsigned_to_nat(0u);
v_ident_630_ = lean_array_fget_borrowed(v_vars_613_, v___x_629_);
v___x_631_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__7));
lean_inc(v_ident_630_);
v___x_632_ = l_Lean_Syntax_isOfKind(v_ident_630_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_dec(v_funName_603_);
v___x_633_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_612_, v_msg_628_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = l_Lean_TSyntax_getId(v_ident_630_);
v___x_635_ = l_Lean_Name_isSuffixOf(v___x_634_, v_funName_603_);
lean_dec(v_funName_603_);
lean_dec(v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_612_, v_msg_628_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_msg_640_; lean_object* v___x_641_; 
v___x_637_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__9, &l_Lean_Elab_TerminationBy_checkVars___closed__9_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__9);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v_msg_628_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__12, &l_Lean_Elab_TerminationBy_checkVars___closed__12_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__12);
v_msg_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_640_, 0, v___x_638_);
lean_ctor_set(v_msg_640_, 1, v___x_639_);
v___x_641_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_612_, v_msg_640_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
return v___x_641_;
}
}
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec_ref(v_a_608_);
lean_dec(v_extraParams_604_);
lean_dec(v_funName_603_);
v___x_642_ = lean_box(0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object* v_funName_644_, lean_object* v_extraParams_645_, lean_object* v_tb_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Elab_TerminationBy_checkVars(v_funName_644_, v_extraParams_645_, v_tb_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_tb_646_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_object* v_00_u03b1_653_, lean_object* v_ref_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_654_, v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object* v_00_u03b1_662_, lean_object* v_ref_663_, lean_object* v_msg_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(v_00_u03b1_662_, v_ref_663_, v_msg_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v_ref_663_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_object* v_00_u03b1_671_, lean_object* v_msg_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_679_, lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_679_, v_msg_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object* v_val_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v_val_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object* v_stx_689_, lean_object* v_terminationBy_x3f_x3f_690_, lean_object* v_terminationBy_x3f_691_, lean_object* v_partialFixpoint_x3f_692_, lean_object* v___x_693_, lean_object* v_toPure_694_, lean_object* v_decreasingBy_x3f_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_696_, 0, v_stx_689_);
lean_ctor_set(v___x_696_, 1, v_terminationBy_x3f_x3f_690_);
lean_ctor_set(v___x_696_, 2, v_terminationBy_x3f_691_);
lean_ctor_set(v___x_696_, 3, v_partialFixpoint_x3f_692_);
lean_ctor_set(v___x_696_, 4, v_decreasingBy_x3f_695_);
lean_ctor_set(v___x_696_, 5, v___x_693_);
v___x_697_ = lean_apply_2(v_toPure_694_, lean_box(0), v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1));
v___x_701_ = l_Lean_stringToMessageData(v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* v_stx_702_, lean_object* v_terminationBy_x3f_x3f_703_, lean_object* v_terminationBy_x3f_704_, lean_object* v___x_705_, lean_object* v_toPure_706_, lean_object* v_d_x3f_707_, lean_object* v_toBind_708_, lean_object* v_toFunctor_709_, lean_object* v___f_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v___x_716_, lean_object* v_partialFixpoint_x3f_717_){
_start:
{
lean_object* v___f_718_; 
lean_inc(v_toPure_706_);
v___f_718_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1), 7, 6);
lean_closure_set(v___f_718_, 0, v_stx_702_);
lean_closure_set(v___f_718_, 1, v_terminationBy_x3f_x3f_703_);
lean_closure_set(v___f_718_, 2, v_terminationBy_x3f_704_);
lean_closure_set(v___f_718_, 3, v_partialFixpoint_x3f_717_);
lean_closure_set(v___f_718_, 4, v___x_705_);
lean_closure_set(v___f_718_, 5, v_toPure_706_);
if (lean_obj_tag(v_d_x3f_707_) == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec_ref(v_inst_715_);
lean_dec_ref(v_inst_714_);
lean_dec_ref(v___x_713_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___f_710_);
lean_dec_ref(v_toFunctor_709_);
v___x_719_ = lean_box(0);
v___x_720_ = lean_apply_2(v_toPure_706_, lean_box(0), v___x_719_);
v___x_721_ = lean_apply_4(v_toBind_708_, lean_box(0), lean_box(0), v___x_720_, v___f_718_);
return v___x_721_;
}
else
{
lean_object* v_val_722_; lean_object* v_map_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_741_; 
v_val_722_ = lean_ctor_get(v_d_x3f_707_, 0);
lean_inc(v_val_722_);
lean_dec_ref(v_d_x3f_707_);
v_map_723_ = lean_ctor_get(v_toFunctor_709_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_toFunctor_709_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_toFunctor_709_, 1);
lean_dec(v_unused_742_);
v___x_725_ = v_toFunctor_709_;
v_isShared_726_ = v_isSharedCheck_741_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_map_723_);
lean_dec(v_toFunctor_709_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_741_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___y_728_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0));
v___x_732_ = l_Lean_Name_mkStr4(v___x_711_, v___x_712_, v___x_713_, v___x_731_);
lean_inc(v_val_722_);
v___x_733_ = l_Lean_Syntax_isOfKind(v_val_722_, v___x_732_);
lean_dec(v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_del_object(v___x_725_);
lean_dec(v_toPure_706_);
v___x_734_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2, &l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2);
v___x_735_ = l_Lean_throwErrorAt___redArg(v_inst_714_, v_inst_715_, v_val_722_, v___x_734_);
v___y_728_ = v___x_735_;
goto v___jp_727_;
}
else
{
lean_object* v_tactic_736_; lean_object* v___x_738_; 
lean_dec_ref(v_inst_715_);
lean_dec_ref(v_inst_714_);
v_tactic_736_ = l_Lean_Syntax_getArg(v_val_722_, v___x_716_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v_tactic_736_);
lean_ctor_set(v___x_725_, 0, v_val_722_);
v___x_738_ = v___x_725_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_val_722_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_tactic_736_);
v___x_738_ = v_reuseFailAlloc_740_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; 
v___x_739_ = lean_apply_2(v_toPure_706_, lean_box(0), v___x_738_);
v___y_728_ = v___x_739_;
goto v___jp_727_;
}
}
v___jp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_apply_4(v_map_723_, lean_box(0), lean_box(0), v___f_710_, v___y_728_);
v___x_730_ = lean_apply_4(v_toBind_708_, lean_box(0), lean_box(0), v___x_729_, v___f_718_);
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object* v_stx_743_, lean_object* v_terminationBy_x3f_x3f_744_, lean_object* v_terminationBy_x3f_745_, lean_object* v___x_746_, lean_object* v_toPure_747_, lean_object* v_d_x3f_748_, lean_object* v_toBind_749_, lean_object* v_toFunctor_750_, lean_object* v___f_751_, lean_object* v___x_752_, lean_object* v___x_753_, lean_object* v___x_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v___x_757_, lean_object* v_partialFixpoint_x3f_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_743_, v_terminationBy_x3f_x3f_744_, v_terminationBy_x3f_745_, v___x_746_, v_toPure_747_, v_d_x3f_748_, v_toBind_749_, v_toFunctor_750_, v___f_751_, v___x_752_, v___x_753_, v___x_754_, v_inst_755_, v_inst_756_, v___x_757_, v_partialFixpoint_x3f_758_);
lean_dec(v___x_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object* v___f_760_, lean_object* v_partialFixpoint_x3f_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_apply_1(v___f_760_, v_partialFixpoint_x3f_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object* v_stx_766_, lean_object* v_terminationBy_x3f_x3f_767_, lean_object* v___x_768_, lean_object* v_toPure_769_, lean_object* v_d_x3f_770_, lean_object* v_toBind_771_, lean_object* v_toFunctor_772_, lean_object* v___f_773_, lean_object* v___x_774_, lean_object* v___x_775_, lean_object* v___x_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v___x_779_, lean_object* v_t_x3f_780_, lean_object* v_terminationBy_x3f_781_){
_start:
{
lean_object* v___f_782_; 
lean_inc(v___x_779_);
lean_inc_ref(v___x_776_);
lean_inc_ref(v___x_775_);
lean_inc_ref(v___x_774_);
lean_inc(v_toBind_771_);
lean_inc(v_toPure_769_);
v___f_782_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed), 16, 15);
lean_closure_set(v___f_782_, 0, v_stx_766_);
lean_closure_set(v___f_782_, 1, v_terminationBy_x3f_x3f_767_);
lean_closure_set(v___f_782_, 2, v_terminationBy_x3f_781_);
lean_closure_set(v___f_782_, 3, v___x_768_);
lean_closure_set(v___f_782_, 4, v_toPure_769_);
lean_closure_set(v___f_782_, 5, v_d_x3f_770_);
lean_closure_set(v___f_782_, 6, v_toBind_771_);
lean_closure_set(v___f_782_, 7, v_toFunctor_772_);
lean_closure_set(v___f_782_, 8, v___f_773_);
lean_closure_set(v___f_782_, 9, v___x_774_);
lean_closure_set(v___f_782_, 10, v___x_775_);
lean_closure_set(v___f_782_, 11, v___x_776_);
lean_closure_set(v___f_782_, 12, v_inst_777_);
lean_closure_set(v___f_782_, 13, v_inst_778_);
lean_closure_set(v___f_782_, 14, v___x_779_);
if (lean_obj_tag(v_t_x3f_780_) == 1)
{
lean_object* v_val_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_860_; 
v_val_783_ = lean_ctor_get(v_t_x3f_780_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_t_x3f_780_);
if (v_isSharedCheck_860_ == 0)
{
v___x_785_ = v_t_x3f_780_;
v_isShared_786_ = v_isSharedCheck_860_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_val_783_);
lean_dec(v_t_x3f_780_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_860_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_787_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_776_);
lean_inc_ref(v___x_775_);
lean_inc_ref(v___x_774_);
v___x_788_ = l_Lean_Name_mkStr4(v___x_774_, v___x_775_, v___x_776_, v___x_787_);
lean_inc(v_val_783_);
v___x_789_ = l_Lean_Syntax_isOfKind(v_val_783_, v___x_788_);
lean_dec(v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_790_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_776_);
lean_inc_ref(v___x_775_);
lean_inc_ref(v___x_774_);
v___x_791_ = l_Lean_Name_mkStr4(v___x_774_, v___x_775_, v___x_776_, v___x_790_);
lean_inc(v_val_783_);
v___x_792_ = l_Lean_Syntax_isOfKind(v_val_783_, v___x_791_);
lean_dec(v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_793_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_794_ = l_Lean_Name_mkStr4(v___x_774_, v___x_775_, v___x_776_, v___x_793_);
lean_inc(v_val_783_);
v___x_795_ = l_Lean_Syntax_isOfKind(v_val_783_, v___x_794_);
lean_dec(v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___f_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_del_object(v___x_785_);
lean_dec(v_val_783_);
lean_dec(v___x_779_);
v___f_796_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_796_, 0, v___f_782_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_apply_2(v_toPure_769_, lean_box(0), v___x_797_);
v___x_799_ = lean_apply_4(v_toBind_771_, lean_box(0), lean_box(0), v___x_798_, v___f_796_);
return v___x_799_;
}
else
{
lean_object* v___f_800_; lean_object* v_term_x3f_802_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___f_800_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_800_, 0, v___f_782_);
v___x_810_ = l_Lean_Syntax_getArg(v_val_783_, v___x_779_);
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
lean_dec(v___x_779_);
v___x_814_ = lean_box(0);
v___x_815_ = lean_apply_2(v_toPure_769_, lean_box(0), v___x_814_);
v___x_816_ = lean_apply_4(v_toBind_771_, lean_box(0), lean_box(0), v___x_815_, v___f_800_);
return v___x_816_;
}
else
{
lean_object* v_term_x3f_817_; lean_object* v___x_818_; 
v_term_x3f_817_ = l_Lean_Syntax_getArg(v___x_810_, v___x_779_);
lean_dec(v___x_779_);
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
lean_dec(v___x_779_);
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
v___x_807_ = lean_apply_2(v_toPure_769_, lean_box(0), v___x_806_);
v___x_808_ = lean_apply_4(v_toBind_771_, lean_box(0), lean_box(0), v___x_807_, v___f_800_);
return v___x_808_;
}
}
}
}
else
{
lean_object* v___f_820_; lean_object* v_term_x3f_822_; lean_object* v___x_830_; uint8_t v___x_831_; 
lean_dec_ref(v___x_776_);
lean_dec_ref(v___x_775_);
lean_dec_ref(v___x_774_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_820_, 0, v___f_782_);
v___x_830_ = l_Lean_Syntax_getArg(v_val_783_, v___x_779_);
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
lean_dec(v___x_779_);
v___x_834_ = lean_box(0);
v___x_835_ = lean_apply_2(v_toPure_769_, lean_box(0), v___x_834_);
v___x_836_ = lean_apply_4(v_toBind_771_, lean_box(0), lean_box(0), v___x_835_, v___f_820_);
return v___x_836_;
}
else
{
lean_object* v_term_x3f_837_; lean_object* v___x_838_; 
v_term_x3f_837_ = l_Lean_Syntax_getArg(v___x_830_, v___x_779_);
lean_dec(v___x_779_);
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
lean_dec(v___x_779_);
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
v___x_827_ = lean_apply_2(v_toPure_769_, lean_box(0), v___x_826_);
v___x_828_ = lean_apply_4(v_toBind_771_, lean_box(0), lean_box(0), v___x_827_, v___f_820_);
return v___x_828_;
}
}
}
}
else
{
lean_object* v___f_840_; lean_object* v_term_x3f_842_; lean_object* v___x_850_; uint8_t v___x_851_; 
lean_dec_ref(v___x_776_);
lean_dec_ref(v___x_775_);
lean_dec_ref(v___x_774_);
v___f_840_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_840_, 0, v___f_782_);
v___x_850_ = l_Lean_Syntax_getArg(v_val_783_, v___x_779_);
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
lean_dec(v___x_779_);
v___x_854_ = lean_box(0);
v___x_855_ = lean_apply_2(v_toPure_769_, lean_box(0), v___x_854_);
v___x_856_ = lean_apply_4(v_toBind_771_, lean_box(0), lean_box(0), v___x_855_, v___f_840_);
return v___x_856_;
}
else
{
lean_object* v_term_x3f_857_; lean_object* v___x_858_; 
v_term_x3f_857_ = l_Lean_Syntax_getArg(v___x_850_, v___x_779_);
lean_dec(v___x_779_);
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
lean_dec(v___x_779_);
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
v___x_847_ = lean_apply_2(v_toPure_769_, lean_box(0), v___x_846_);
v___x_848_ = lean_apply_4(v_toBind_771_, lean_box(0), lean_box(0), v___x_847_, v___f_840_);
return v___x_848_;
}
}
}
}
}
else
{
lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v_t_x3f_780_);
lean_dec(v___x_779_);
lean_dec_ref(v___x_776_);
lean_dec_ref(v___x_775_);
lean_dec_ref(v___x_774_);
v___f_861_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_861_, 0, v___f_782_);
v___x_862_ = lean_box(0);
v___x_863_ = lean_apply_2(v_toPure_769_, lean_box(0), v___x_862_);
v___x_864_ = lean_apply_4(v_toBind_771_, lean_box(0), lean_box(0), v___x_863_, v___f_861_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* v___f_865_, lean_object* v_terminationBy_x3f_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = lean_apply_1(v___f_865_, v_terminationBy_x3f_866_);
return v___x_867_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2));
v___x_872_ = l_Lean_stringToMessageData(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4));
v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* v_stx_876_, lean_object* v___x_877_, lean_object* v_toPure_878_, lean_object* v_d_x3f_879_, lean_object* v_toBind_880_, lean_object* v_toFunctor_881_, lean_object* v___f_882_, lean_object* v___x_883_, lean_object* v___x_884_, lean_object* v___x_885_, lean_object* v_inst_886_, lean_object* v_inst_887_, lean_object* v___x_888_, lean_object* v_t_x3f_889_, lean_object* v_terminationBy_x3f_x3f_890_){
_start:
{
lean_object* v___f_891_; 
lean_inc(v_t_x3f_889_);
lean_inc(v___x_888_);
lean_inc_ref(v_inst_887_);
lean_inc_ref(v_inst_886_);
lean_inc_ref(v___x_885_);
lean_inc_ref(v___x_884_);
lean_inc_ref(v___x_883_);
lean_inc(v_toBind_880_);
lean_inc(v_toPure_878_);
lean_inc(v___x_877_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11), 16, 15);
lean_closure_set(v___f_891_, 0, v_stx_876_);
lean_closure_set(v___f_891_, 1, v_terminationBy_x3f_x3f_890_);
lean_closure_set(v___f_891_, 2, v___x_877_);
lean_closure_set(v___f_891_, 3, v_toPure_878_);
lean_closure_set(v___f_891_, 4, v_d_x3f_879_);
lean_closure_set(v___f_891_, 5, v_toBind_880_);
lean_closure_set(v___f_891_, 6, v_toFunctor_881_);
lean_closure_set(v___f_891_, 7, v___f_882_);
lean_closure_set(v___f_891_, 8, v___x_883_);
lean_closure_set(v___f_891_, 9, v___x_884_);
lean_closure_set(v___f_891_, 10, v___x_885_);
lean_closure_set(v___f_891_, 11, v_inst_886_);
lean_closure_set(v___f_891_, 12, v_inst_887_);
lean_closure_set(v___f_891_, 13, v___x_888_);
lean_closure_set(v___f_891_, 14, v_t_x3f_889_);
if (lean_obj_tag(v_t_x3f_889_) == 1)
{
lean_object* v_val_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_1004_; 
v_val_892_ = lean_ctor_get(v_t_x3f_889_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_t_x3f_889_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_894_ = v_t_x3f_889_;
v_isShared_895_ = v_isSharedCheck_1004_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_val_892_);
lean_dec(v_t_x3f_889_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_1004_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_896_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0));
lean_inc_ref(v___x_885_);
lean_inc_ref(v___x_884_);
lean_inc_ref(v___x_883_);
v___x_897_ = l_Lean_Name_mkStr4(v___x_883_, v___x_884_, v___x_885_, v___x_896_);
lean_inc(v_val_892_);
v___x_898_ = l_Lean_Syntax_isOfKind(v_val_892_, v___x_897_);
lean_dec(v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
lean_del_object(v___x_894_);
lean_dec(v___x_877_);
v___x_899_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1));
lean_inc_ref(v___x_885_);
lean_inc_ref(v___x_884_);
lean_inc_ref(v___x_883_);
v___x_900_ = l_Lean_Name_mkStr4(v___x_883_, v___x_884_, v___x_885_, v___x_899_);
lean_inc(v_val_892_);
v___x_901_ = l_Lean_Syntax_isOfKind(v_val_892_, v___x_900_);
lean_dec(v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_885_);
lean_inc_ref(v___x_884_);
lean_inc_ref(v___x_883_);
v___x_903_ = l_Lean_Name_mkStr4(v___x_883_, v___x_884_, v___x_885_, v___x_902_);
lean_inc(v_val_892_);
v___x_904_ = l_Lean_Syntax_isOfKind(v_val_892_, v___x_903_);
lean_dec(v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_905_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_885_);
lean_inc_ref(v___x_884_);
lean_inc_ref(v___x_883_);
v___x_906_ = l_Lean_Name_mkStr4(v___x_883_, v___x_884_, v___x_885_, v___x_905_);
lean_inc(v_val_892_);
v___x_907_ = l_Lean_Syntax_isOfKind(v_val_892_, v___x_906_);
lean_dec(v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_908_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_909_ = l_Lean_Name_mkStr4(v___x_883_, v___x_884_, v___x_885_, v___x_908_);
lean_inc(v_val_892_);
v___x_910_ = l_Lean_Syntax_isOfKind(v_val_892_, v___x_909_);
lean_dec(v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v___x_888_);
lean_dec(v_toPure_878_);
v___f_911_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_911_, 0, v___f_891_);
v___x_912_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_913_ = l_Lean_throwErrorAt___redArg(v_inst_886_, v_inst_887_, v_val_892_, v___x_912_);
v___x_914_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_913_, v___f_911_);
return v___x_914_;
}
else
{
lean_object* v___f_915_; lean_object* v___x_920_; uint8_t v___x_921_; 
v___f_915_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_915_, 0, v___f_891_);
v___x_920_ = l_Lean_Syntax_getArg(v_val_892_, v___x_888_);
lean_dec(v___x_888_);
v___x_921_ = l_Lean_Syntax_isNone(v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_922_ = lean_unsigned_to_nat(2u);
v___x_923_ = l_Lean_Syntax_matchesNull(v___x_920_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v_toPure_878_);
v___x_924_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_925_ = l_Lean_throwErrorAt___redArg(v_inst_886_, v_inst_887_, v_val_892_, v___x_924_);
v___x_926_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_925_, v___f_915_);
return v___x_926_;
}
else
{
lean_dec(v_val_892_);
lean_dec_ref(v_inst_887_);
lean_dec_ref(v_inst_886_);
goto v___jp_916_;
}
}
else
{
lean_dec(v___x_920_);
lean_dec(v_val_892_);
lean_dec_ref(v_inst_887_);
lean_dec_ref(v_inst_886_);
goto v___jp_916_;
}
v___jp_916_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_box(0);
v___x_918_ = lean_apply_2(v_toPure_878_, lean_box(0), v___x_917_);
v___x_919_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_918_, v___f_915_);
return v___x_919_;
}
}
}
else
{
lean_object* v___f_927_; lean_object* v___x_932_; uint8_t v___x_933_; 
lean_dec_ref(v___x_885_);
lean_dec_ref(v___x_884_);
lean_dec_ref(v___x_883_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_927_, 0, v___f_891_);
v___x_932_ = l_Lean_Syntax_getArg(v_val_892_, v___x_888_);
lean_dec(v___x_888_);
v___x_933_ = l_Lean_Syntax_isNone(v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_934_ = lean_unsigned_to_nat(2u);
v___x_935_ = l_Lean_Syntax_matchesNull(v___x_932_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v_toPure_878_);
v___x_936_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_937_ = l_Lean_throwErrorAt___redArg(v_inst_886_, v_inst_887_, v_val_892_, v___x_936_);
v___x_938_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_937_, v___f_927_);
return v___x_938_;
}
else
{
lean_dec(v_val_892_);
lean_dec_ref(v_inst_887_);
lean_dec_ref(v_inst_886_);
goto v___jp_928_;
}
}
else
{
lean_dec(v___x_932_);
lean_dec(v_val_892_);
lean_dec_ref(v_inst_887_);
lean_dec_ref(v_inst_886_);
goto v___jp_928_;
}
v___jp_928_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_box(0);
v___x_930_ = lean_apply_2(v_toPure_878_, lean_box(0), v___x_929_);
v___x_931_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_930_, v___f_927_);
return v___x_931_;
}
}
}
else
{
lean_object* v___f_939_; lean_object* v___x_944_; uint8_t v___x_945_; 
lean_dec_ref(v___x_885_);
lean_dec_ref(v___x_884_);
lean_dec_ref(v___x_883_);
v___f_939_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_939_, 0, v___f_891_);
v___x_944_ = l_Lean_Syntax_getArg(v_val_892_, v___x_888_);
lean_dec(v___x_888_);
v___x_945_ = l_Lean_Syntax_isNone(v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_unsigned_to_nat(2u);
v___x_947_ = l_Lean_Syntax_matchesNull(v___x_944_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v_toPure_878_);
v___x_948_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_949_ = l_Lean_throwErrorAt___redArg(v_inst_886_, v_inst_887_, v_val_892_, v___x_948_);
v___x_950_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_949_, v___f_939_);
return v___x_950_;
}
else
{
lean_dec(v_val_892_);
lean_dec_ref(v_inst_887_);
lean_dec_ref(v_inst_886_);
goto v___jp_940_;
}
}
else
{
lean_dec(v___x_944_);
lean_dec(v_val_892_);
lean_dec_ref(v_inst_887_);
lean_dec_ref(v_inst_886_);
goto v___jp_940_;
}
v___jp_940_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_box(0);
v___x_942_ = lean_apply_2(v_toPure_878_, lean_box(0), v___x_941_);
v___x_943_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_942_, v___f_939_);
return v___x_943_;
}
}
}
else
{
lean_object* v___f_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec(v_val_892_);
lean_dec(v___x_888_);
lean_dec_ref(v_inst_887_);
lean_dec_ref(v_inst_886_);
lean_dec_ref(v___x_885_);
lean_dec_ref(v___x_884_);
lean_dec_ref(v___x_883_);
v___f_951_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_951_, 0, v___f_891_);
v___x_952_ = lean_box(0);
v___x_953_ = lean_apply_2(v_toPure_878_, lean_box(0), v___x_952_);
v___x_954_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_953_, v___f_951_);
return v___x_954_;
}
}
else
{
lean_object* v___f_955_; lean_object* v___y_957_; uint8_t v___y_958_; lean_object* v___y_959_; uint8_t v___y_960_; lean_object* v___y_968_; uint8_t v___y_969_; uint8_t v___y_970_; lean_object* v_s_977_; lean_object* v___x_995_; uint8_t v___x_996_; 
lean_dec_ref(v___x_885_);
lean_dec_ref(v___x_884_);
lean_dec_ref(v___x_883_);
v___f_955_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_955_, 0, v___f_891_);
v___x_995_ = l_Lean_Syntax_getArg(v_val_892_, v___x_888_);
v___x_996_ = l_Lean_Syntax_isNone(v___x_995_);
if (v___x_996_ == 0)
{
uint8_t v___x_997_; 
lean_inc(v___x_995_);
v___x_997_ = l_Lean_Syntax_matchesNull(v___x_995_, v___x_888_);
lean_dec(v___x_888_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec(v___x_995_);
lean_del_object(v___x_894_);
lean_dec(v_toPure_878_);
lean_dec(v___x_877_);
v___x_998_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_999_ = l_Lean_throwErrorAt___redArg(v_inst_886_, v_inst_887_, v_val_892_, v___x_998_);
v___x_1000_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_999_, v___f_955_);
return v___x_1000_;
}
else
{
lean_object* v_s_1001_; lean_object* v___x_1002_; 
v_s_1001_ = l_Lean_Syntax_getArg(v___x_995_, v___x_877_);
lean_dec(v___x_995_);
v___x_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1002_, 0, v_s_1001_);
v_s_977_ = v___x_1002_;
goto v___jp_976_;
}
}
else
{
lean_object* v___x_1003_; 
lean_dec(v___x_995_);
lean_dec(v___x_888_);
v___x_1003_ = lean_box(0);
v_s_977_ = v___x_1003_;
goto v___jp_976_;
}
v___jp_956_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_961_, 0, v_val_892_);
lean_ctor_set(v___x_961_, 1, v___y_959_);
lean_ctor_set(v___x_961_, 2, v___y_957_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*3, v___y_960_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*3 + 1, v___y_958_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_961_);
v___x_963_ = v___x_894_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_966_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_apply_2(v_toPure_878_, lean_box(0), v___x_963_);
v___x_965_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_964_, v___f_955_);
return v___x_965_;
}
}
v___jp_967_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_971_ = lean_mk_empty_array_with_capacity(v___x_877_);
lean_dec(v___x_877_);
v___x_972_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_972_, 0, v_val_892_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
lean_ctor_set(v___x_972_, 2, v___y_968_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*3, v___y_970_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*3 + 1, v___y_969_);
v___x_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
v___x_974_ = lean_apply_2(v_toPure_878_, lean_box(0), v___x_973_);
v___x_975_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_974_, v___f_955_);
return v___x_975_;
}
v___jp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_978_ = lean_unsigned_to_nat(2u);
v___x_979_ = l_Lean_Syntax_getArg(v_val_892_, v___x_978_);
lean_inc(v___x_979_);
v___x_980_ = l_Lean_Syntax_matchesNull(v___x_979_, v___x_978_);
if (v___x_980_ == 0)
{
uint8_t v___x_981_; 
lean_del_object(v___x_894_);
v___x_981_ = l_Lean_Syntax_matchesNull(v___x_979_, v___x_877_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec(v_s_977_);
lean_dec(v_toPure_878_);
lean_dec(v___x_877_);
v___x_982_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_983_ = l_Lean_throwErrorAt___redArg(v_inst_886_, v_inst_887_, v_val_892_, v___x_982_);
v___x_984_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_983_, v___f_955_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; lean_object* v_body_986_; 
lean_dec_ref(v_inst_887_);
lean_dec_ref(v_inst_886_);
v___x_985_ = lean_unsigned_to_nat(3u);
v_body_986_ = l_Lean_Syntax_getArg(v_val_892_, v___x_985_);
if (lean_obj_tag(v_s_977_) == 0)
{
v___y_968_ = v_body_986_;
v___y_969_ = v___x_980_;
v___y_970_ = v___x_980_;
goto v___jp_967_;
}
else
{
lean_dec_ref(v_s_977_);
v___y_968_ = v_body_986_;
v___y_969_ = v___x_980_;
v___y_970_ = v___x_981_;
goto v___jp_967_;
}
}
}
else
{
lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_987_ = l_Lean_Syntax_getArg(v___x_979_, v___x_877_);
lean_dec(v___x_979_);
lean_inc(v___x_987_);
v___x_988_ = l_Lean_Syntax_matchesNull(v___x_987_, v___x_877_);
lean_dec(v___x_877_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v_body_990_; lean_object* v_vars_991_; 
lean_dec_ref(v_inst_887_);
lean_dec_ref(v_inst_886_);
v___x_989_ = lean_unsigned_to_nat(3u);
v_body_990_ = l_Lean_Syntax_getArg(v_val_892_, v___x_989_);
v_vars_991_ = l_Lean_Syntax_getArgs(v___x_987_);
lean_dec(v___x_987_);
if (lean_obj_tag(v_s_977_) == 0)
{
v___y_957_ = v_body_990_;
v___y_958_ = v___x_988_;
v___y_959_ = v_vars_991_;
v___y_960_ = v___x_988_;
goto v___jp_956_;
}
else
{
lean_dec_ref(v_s_977_);
v___y_957_ = v_body_990_;
v___y_958_ = v___x_988_;
v___y_959_ = v_vars_991_;
v___y_960_ = v___x_980_;
goto v___jp_956_;
}
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec(v___x_987_);
lean_dec(v_s_977_);
lean_del_object(v___x_894_);
lean_dec(v_toPure_878_);
v___x_992_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
v___x_993_ = l_Lean_throwErrorAt___redArg(v_inst_886_, v_inst_887_, v_val_892_, v___x_992_);
v___x_994_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_993_, v___f_955_);
return v___x_994_;
}
}
}
}
}
}
else
{
lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec(v_t_x3f_889_);
lean_dec(v___x_888_);
lean_dec_ref(v_inst_887_);
lean_dec_ref(v_inst_886_);
lean_dec_ref(v___x_885_);
lean_dec_ref(v___x_884_);
lean_dec_ref(v___x_883_);
lean_dec(v___x_877_);
v___f_1005_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1005_, 0, v___f_891_);
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_apply_2(v_toPure_878_, lean_box(0), v___x_1006_);
v___x_1008_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_1007_, v___f_1005_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* v___f_1009_, lean_object* v_terminationBy_x3f_x3f_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_apply_1(v___f_1009_, v_terminationBy_x3f_x3f_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_stx_1036_){
_start:
{
if (lean_obj_tag(v_stx_1036_) == 0)
{
lean_object* v_toApplicative_1037_; lean_object* v_toPure_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1049_; 
v_toApplicative_1037_ = lean_ctor_get(v_inst_1034_, 0);
lean_inc_ref(v_toApplicative_1037_);
lean_dec_ref(v_inst_1035_);
lean_dec_ref(v_inst_1034_);
v_toPure_1038_ = lean_ctor_get(v_toApplicative_1037_, 1);
lean_inc(v_toPure_1038_);
lean_dec_ref(v_toApplicative_1037_);
v___x_1039_ = ((lean_object*)(l_Lean_Elab_TerminationHints_none));
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; lean_object* v_unused_1051_; lean_object* v_unused_1052_; lean_object* v_unused_1053_; lean_object* v_unused_1054_; lean_object* v_unused_1055_; 
v_unused_1050_ = lean_ctor_get(v___x_1039_, 5);
lean_dec(v_unused_1050_);
v_unused_1051_ = lean_ctor_get(v___x_1039_, 4);
lean_dec(v_unused_1051_);
v_unused_1052_ = lean_ctor_get(v___x_1039_, 3);
lean_dec(v_unused_1052_);
v_unused_1053_ = lean_ctor_get(v___x_1039_, 2);
lean_dec(v_unused_1053_);
v_unused_1054_ = lean_ctor_get(v___x_1039_, 1);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v___x_1039_, 0);
lean_dec(v_unused_1055_);
v___x_1041_ = v___x_1039_;
v_isShared_1042_ = v_isSharedCheck_1049_;
goto v_resetjp_1040_;
}
else
{
lean_dec(v___x_1039_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1049_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = lean_box(0);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 5, v___x_1043_);
lean_ctor_set(v___x_1041_, 4, v___x_1044_);
lean_ctor_set(v___x_1041_, 3, v___x_1044_);
lean_ctor_set(v___x_1041_, 2, v___x_1044_);
lean_ctor_set(v___x_1041_, 1, v___x_1044_);
lean_ctor_set(v___x_1041_, 0, v_stx_1036_);
v___x_1046_ = v___x_1041_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_stx_1036_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1048_, 3, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1048_, 4, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1048_, 5, v___x_1043_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_apply_2(v_toPure_1038_, lean_box(0), v___x_1046_);
return v___x_1047_;
}
}
}
else
{
lean_object* v_toApplicative_1056_; lean_object* v_toBind_1057_; lean_object* v_toFunctor_1058_; lean_object* v_toPure_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v_toApplicative_1056_ = lean_ctor_get(v_inst_1034_, 0);
v_toBind_1057_ = lean_ctor_get(v_inst_1034_, 1);
v_toFunctor_1058_ = lean_ctor_get(v_toApplicative_1056_, 0);
v_toPure_1059_ = lean_ctor_get(v_toApplicative_1056_, 1);
v___x_1060_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__0));
v___x_1061_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__1));
v___x_1062_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__2));
v___x_1063_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__4));
lean_inc(v_stx_1036_);
v___x_1064_ = l_Lean_Syntax_isOfKind(v_stx_1036_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1065_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1066_ = lean_box(0);
lean_inc(v_stx_1036_);
v___x_1067_ = l_Lean_Syntax_formatStx(v_stx_1036_, v___x_1066_, v___x_1064_);
v___x_1068_ = l_Std_Format_defWidth;
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = l_Std_Format_pretty(v___x_1067_, v___x_1068_, v___x_1069_, v___x_1069_);
v___x_1071_ = lean_string_append(v___x_1065_, v___x_1070_);
lean_dec_ref(v___x_1070_);
v___x_1072_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1073_ = lean_string_append(v___x_1071_, v___x_1072_);
lean_inc(v_stx_1036_);
v___x_1074_ = l_Lean_Syntax_getKind(v_stx_1036_);
v___x_1075_ = 1;
v___x_1076_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1074_, v___x_1075_);
v___x_1077_ = lean_string_append(v___x_1073_, v___x_1076_);
lean_dec_ref(v___x_1076_);
v___x_1078_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
v___x_1079_ = l_Lean_MessageData_ofFormat(v___x_1078_);
v___x_1080_ = l_Lean_throwErrorAt___redArg(v_inst_1034_, v_inst_1035_, v_stx_1036_, v___x_1079_);
return v___x_1080_;
}
else
{
lean_object* v___f_1081_; lean_object* v___x_1082_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v_d_x3f_1086_; lean_object* v_t_x3f_1110_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___f_1081_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__7));
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1148_ = l_Lean_Syntax_getArg(v_stx_1036_, v___x_1082_);
v___x_1149_ = l_Lean_Syntax_isNone(v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1148_);
v___x_1151_ = l_Lean_Syntax_matchesNull(v___x_1148_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec(v___x_1148_);
v___x_1152_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1153_ = lean_box(0);
lean_inc(v_stx_1036_);
v___x_1154_ = l_Lean_Syntax_formatStx(v_stx_1036_, v___x_1153_, v___x_1151_);
v___x_1155_ = l_Std_Format_defWidth;
v___x_1156_ = l_Std_Format_pretty(v___x_1154_, v___x_1155_, v___x_1082_, v___x_1082_);
v___x_1157_ = lean_string_append(v___x_1152_, v___x_1156_);
lean_dec_ref(v___x_1156_);
v___x_1158_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1159_ = lean_string_append(v___x_1157_, v___x_1158_);
lean_inc(v_stx_1036_);
v___x_1160_ = l_Lean_Syntax_getKind(v_stx_1036_);
v___x_1161_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1160_, v___x_1064_);
v___x_1162_ = lean_string_append(v___x_1159_, v___x_1161_);
lean_dec_ref(v___x_1161_);
v___x_1163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
v___x_1164_ = l_Lean_MessageData_ofFormat(v___x_1163_);
v___x_1165_ = l_Lean_throwErrorAt___redArg(v_inst_1034_, v_inst_1035_, v_stx_1036_, v___x_1164_);
return v___x_1165_;
}
else
{
lean_object* v_t_x3f_1166_; lean_object* v___x_1167_; 
v_t_x3f_1166_ = l_Lean_Syntax_getArg(v___x_1148_, v___x_1082_);
lean_dec(v___x_1148_);
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_t_x3f_1166_);
v_t_x3f_1110_ = v___x_1167_;
goto v___jp_1109_;
}
}
else
{
lean_object* v___x_1168_; 
lean_dec(v___x_1148_);
v___x_1168_ = lean_box(0);
v_t_x3f_1110_ = v___x_1168_;
goto v___jp_1109_;
}
v___jp_1083_:
{
lean_object* v___f_1087_; 
lean_inc(v___y_1085_);
lean_inc(v_toBind_1057_);
lean_inc(v_toPure_1059_);
v___f_1087_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19), 15, 14);
lean_closure_set(v___f_1087_, 0, v_stx_1036_);
lean_closure_set(v___f_1087_, 1, v___x_1082_);
lean_closure_set(v___f_1087_, 2, v_toPure_1059_);
lean_closure_set(v___f_1087_, 3, v_d_x3f_1086_);
lean_closure_set(v___f_1087_, 4, v_toBind_1057_);
lean_closure_set(v___f_1087_, 5, v_toFunctor_1058_);
lean_closure_set(v___f_1087_, 6, v___f_1081_);
lean_closure_set(v___f_1087_, 7, v___x_1060_);
lean_closure_set(v___f_1087_, 8, v___x_1061_);
lean_closure_set(v___f_1087_, 9, v___x_1062_);
lean_closure_set(v___f_1087_, 10, v_inst_1034_);
lean_closure_set(v___f_1087_, 11, v_inst_1035_);
lean_closure_set(v___f_1087_, 12, v___y_1084_);
lean_closure_set(v___f_1087_, 13, v___y_1085_);
if (lean_obj_tag(v___y_1085_) == 1)
{
lean_object* v_val_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1104_; 
v_val_1088_ = lean_ctor_get(v___y_1085_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___y_1085_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1090_ = v___y_1085_;
v_isShared_1091_ = v_isSharedCheck_1104_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_val_1088_);
lean_dec(v___y_1085_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1104_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__8));
lean_inc(v_val_1088_);
v___x_1093_ = l_Lean_Syntax_isOfKind(v_val_1088_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_del_object(v___x_1090_);
lean_dec(v_val_1088_);
v___f_1094_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1094_, 0, v___f_1087_);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_apply_2(v_toPure_1059_, lean_box(0), v___x_1095_);
v___x_1097_ = lean_apply_4(v_toBind_1057_, lean_box(0), lean_box(0), v___x_1096_, v___f_1094_);
return v___x_1097_;
}
else
{
lean_object* v___f_1098_; lean_object* v___x_1100_; 
v___f_1098_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1098_, 0, v___f_1087_);
if (v_isShared_1091_ == 0)
{
v___x_1100_ = v___x_1090_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_val_1088_);
v___x_1100_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_apply_2(v_toPure_1059_, lean_box(0), v___x_1100_);
v___x_1102_ = lean_apply_4(v_toBind_1057_, lean_box(0), lean_box(0), v___x_1101_, v___f_1098_);
return v___x_1102_;
}
}
}
}
else
{
lean_object* v___f_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v___y_1085_);
v___f_1105_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1105_, 0, v___f_1087_);
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_apply_2(v_toPure_1059_, lean_box(0), v___x_1106_);
v___x_1108_ = lean_apply_4(v_toBind_1057_, lean_box(0), lean_box(0), v___x_1107_, v___f_1105_);
return v___x_1108_;
}
}
v___jp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = l_Lean_Syntax_getArg(v_stx_1036_, v___x_1111_);
v___x_1113_ = l_Lean_Syntax_isNone(v___x_1112_);
if (v___x_1113_ == 0)
{
uint8_t v___x_1114_; 
lean_inc(v___x_1112_);
v___x_1114_ = l_Lean_Syntax_matchesNull(v___x_1112_, v___x_1111_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec(v___x_1112_);
lean_dec(v_t_x3f_1110_);
v___x_1115_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1116_ = lean_box(0);
lean_inc(v_stx_1036_);
v___x_1117_ = l_Lean_Syntax_formatStx(v_stx_1036_, v___x_1116_, v___x_1114_);
v___x_1118_ = l_Std_Format_defWidth;
v___x_1119_ = l_Std_Format_pretty(v___x_1117_, v___x_1118_, v___x_1082_, v___x_1082_);
v___x_1120_ = lean_string_append(v___x_1115_, v___x_1119_);
lean_dec_ref(v___x_1119_);
v___x_1121_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1122_ = lean_string_append(v___x_1120_, v___x_1121_);
lean_inc(v_stx_1036_);
v___x_1123_ = l_Lean_Syntax_getKind(v_stx_1036_);
v___x_1124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1123_, v___x_1064_);
v___x_1125_ = lean_string_append(v___x_1122_, v___x_1124_);
lean_dec_ref(v___x_1124_);
v___x_1126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
v___x_1127_ = l_Lean_MessageData_ofFormat(v___x_1126_);
v___x_1128_ = l_Lean_throwErrorAt___redArg(v_inst_1034_, v_inst_1035_, v_stx_1036_, v___x_1127_);
return v___x_1128_;
}
else
{
lean_object* v_d_x3f_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v_d_x3f_1129_ = l_Lean_Syntax_getArg(v___x_1112_, v___x_1082_);
lean_dec(v___x_1112_);
v___x_1130_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__9));
lean_inc(v_d_x3f_1129_);
v___x_1131_ = l_Lean_Syntax_isOfKind(v_d_x3f_1129_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v_d_x3f_1129_);
lean_dec(v_t_x3f_1110_);
v___x_1132_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1133_ = lean_box(0);
lean_inc(v_stx_1036_);
v___x_1134_ = l_Lean_Syntax_formatStx(v_stx_1036_, v___x_1133_, v___x_1131_);
v___x_1135_ = l_Std_Format_defWidth;
v___x_1136_ = l_Std_Format_pretty(v___x_1134_, v___x_1135_, v___x_1082_, v___x_1082_);
v___x_1137_ = lean_string_append(v___x_1132_, v___x_1136_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1139_ = lean_string_append(v___x_1137_, v___x_1138_);
lean_inc(v_stx_1036_);
v___x_1140_ = l_Lean_Syntax_getKind(v_stx_1036_);
v___x_1141_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1140_, v___x_1114_);
v___x_1142_ = lean_string_append(v___x_1139_, v___x_1141_);
lean_dec_ref(v___x_1141_);
v___x_1143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
v___x_1144_ = l_Lean_MessageData_ofFormat(v___x_1143_);
v___x_1145_ = l_Lean_throwErrorAt___redArg(v_inst_1034_, v_inst_1035_, v_stx_1036_, v___x_1144_);
return v___x_1145_;
}
else
{
lean_object* v___x_1146_; 
lean_inc(v_toPure_1059_);
lean_inc_ref(v_toFunctor_1058_);
lean_inc(v_toBind_1057_);
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_d_x3f_1129_);
v___y_1084_ = v___x_1111_;
v___y_1085_ = v_t_x3f_1110_;
v_d_x3f_1086_ = v___x_1146_;
goto v___jp_1083_;
}
}
}
else
{
lean_object* v___x_1147_; 
lean_inc(v_toPure_1059_);
lean_inc_ref(v_toFunctor_1058_);
lean_inc(v_toBind_1057_);
lean_dec(v___x_1112_);
v___x_1147_ = lean_box(0);
v___y_1084_ = v___x_1111_;
v___y_1085_ = v_t_x3f_1110_;
v_d_x3f_1086_ = v___x_1147_;
goto v___jp_1083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* v_m_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_stx_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Elab_elabTerminationHints___redArg(v_inst_1170_, v_inst_1171_, v_stx_1172_);
return v___x_1173_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_TerminationHint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
