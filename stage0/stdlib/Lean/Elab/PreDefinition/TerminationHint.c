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
v___x_127_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
lean_ctor_set(v___x_127_, 2, v___x_126_);
lean_ctor_set(v___x_127_, 3, v___x_126_);
lean_ctor_set(v___x_127_, 4, v___x_125_);
lean_ctor_set(v___x_127_, 5, v___x_125_);
lean_ctor_set(v___x_127_, 6, v___x_125_);
lean_ctor_set(v___x_127_, 7, v___x_125_);
lean_ctor_set(v___x_127_, 8, v___x_125_);
lean_ctor_set(v___x_127_, 9, v___x_125_);
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
uint8_t v___y_3124__boxed_197_; uint8_t v_suppressElabErrors_boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v___y_3124__boxed_197_ = lean_unbox(v___y_194_);
v_suppressElabErrors_boxed_198_ = lean_unbox(v_suppressElabErrors_195_);
v_res_199_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v___y_3124__boxed_197_, v_suppressElabErrors_boxed_198_, v_x_196_);
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
lean_object* v___y_224_; uint8_t v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; uint8_t v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; uint8_t v___y_263_; lean_object* v___y_264_; uint8_t v___y_265_; uint8_t v___y_266_; lean_object* v___y_267_; lean_object* v___y_285_; lean_object* v___y_286_; uint8_t v___y_287_; uint8_t v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; uint8_t v___y_291_; lean_object* v___y_292_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; uint8_t v___y_299_; lean_object* v___y_300_; uint8_t v___y_301_; uint8_t v___y_302_; uint8_t v___x_307_; lean_object* v___y_309_; lean_object* v___y_310_; uint8_t v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; uint8_t v___y_314_; uint8_t v___y_315_; uint8_t v___y_317_; uint8_t v___x_332_; 
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
v_openDecls_235_ = lean_ctor_get(v___y_231_, 7);
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
lean_inc(v_openDecls_235_);
lean_inc(v_currNamespace_234_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_currNamespace_234_);
lean_ctor_set(v___x_248_, 1, v_openDecls_235_);
v___x_249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___y_227_);
lean_inc_ref(v___y_229_);
lean_inc_ref(v___y_226_);
v___x_250_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_250_, 0, v___y_226_);
lean_ctor_set(v___x_250_, 1, v___y_230_);
lean_ctor_set(v___x_250_, 2, v___y_224_);
lean_ctor_set(v___x_250_, 3, v___y_229_);
lean_ctor_set(v___x_250_, 4, v___x_249_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*5, v___y_225_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*5 + 1, v___y_228_);
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
lean_inc_ref_n(v___y_261_, 2);
v___x_274_ = l_Lean_FileMap_toPosition(v___y_261_, v___y_262_);
lean_dec(v___y_262_);
v___x_275_ = l_Lean_FileMap_toPosition(v___y_261_, v___y_267_);
lean_dec(v___y_267_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
v___x_277_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0));
if (v___y_263_ == 0)
{
lean_del_object(v___x_272_);
lean_dec_ref(v___y_260_);
v___y_224_ = v___x_276_;
v___y_225_ = v___y_265_;
v___y_226_ = v___y_264_;
v___y_227_ = v_a_270_;
v___y_228_ = v___y_266_;
v___y_229_ = v___x_277_;
v___y_230_ = v___x_274_;
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
v___y_225_ = v___y_265_;
v___y_226_ = v___y_264_;
v___y_227_ = v_a_270_;
v___y_228_ = v___y_266_;
v___y_229_ = v___x_277_;
v___y_230_ = v___x_274_;
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
v___x_293_ = l_Lean_Syntax_getTailPos_x3f(v___y_290_, v___y_288_);
lean_dec(v___y_290_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_inc(v___y_292_);
v___y_260_ = v___y_285_;
v___y_261_ = v___y_286_;
v___y_262_ = v___y_292_;
v___y_263_ = v___y_287_;
v___y_264_ = v___y_289_;
v___y_265_ = v___y_288_;
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
v___y_264_ = v___y_289_;
v___y_265_ = v___y_288_;
v___y_266_ = v___y_291_;
v___y_267_ = v_val_294_;
goto v___jp_259_;
}
}
v___jp_295_:
{
lean_object* v_ref_303_; lean_object* v___x_304_; 
v_ref_303_ = l_Lean_replaceRef(v_ref_216_, v___y_297_);
v___x_304_ = l_Lean_Syntax_getPos_x3f(v_ref_303_, v___y_301_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_unsigned_to_nat(0u);
v___y_285_ = v___y_296_;
v___y_286_ = v___y_298_;
v___y_287_ = v___y_299_;
v___y_288_ = v___y_301_;
v___y_289_ = v___y_300_;
v___y_290_ = v_ref_303_;
v___y_291_ = v___y_302_;
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
v___y_286_ = v___y_298_;
v___y_287_ = v___y_299_;
v___y_288_ = v___y_301_;
v___y_289_ = v___y_300_;
v___y_290_ = v_ref_303_;
v___y_291_ = v___y_302_;
v___y_292_ = v_val_306_;
goto v___jp_284_;
}
}
v___jp_308_:
{
if (v___y_315_ == 0)
{
v___y_296_ = v___y_313_;
v___y_297_ = v___y_309_;
v___y_298_ = v___y_310_;
v___y_299_ = v___y_311_;
v___y_300_ = v___y_312_;
v___y_301_ = v___y_314_;
v___y_302_ = v_severity_218_;
goto v___jp_295_;
}
else
{
v___y_296_ = v___y_313_;
v___y_297_ = v___y_309_;
v___y_298_ = v___y_310_;
v___y_299_ = v___y_311_;
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
v___y_309_ = v_ref_321_;
v___y_310_ = v_fileMap_319_;
v___y_311_ = v_suppressElabErrors_322_;
v___y_312_ = v_fileName_318_;
v___y_313_ = v___f_325_;
v___y_314_ = v___y_317_;
v___y_315_ = v___x_327_;
goto v___jp_308_;
}
else
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = l_Lean_warningAsError;
v___x_329_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_options_320_, v___x_328_);
v___y_309_ = v_ref_321_;
v___y_310_ = v_fileMap_319_;
v___y_311_ = v_suppressElabErrors_322_;
v___y_312_ = v_fileName_318_;
v___y_313_ = v___f_325_;
v___y_314_ = v___y_317_;
v___y_315_ = v___x_329_;
goto v___jp_308_;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
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
lean_dec_ref(v___y_338_);
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
lean_dec_ref(v___y_354_);
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
lean_dec_ref(v_a_441_);
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
lean_object* v_fileName_550_; lean_object* v_fileMap_551_; lean_object* v_options_552_; lean_object* v_currRecDepth_553_; lean_object* v_maxRecDepth_554_; lean_object* v_ref_555_; lean_object* v_currNamespace_556_; lean_object* v_openDecls_557_; lean_object* v_initHeartbeats_558_; lean_object* v_maxHeartbeats_559_; lean_object* v_quotContext_560_; lean_object* v_currMacroScope_561_; uint8_t v_diag_562_; lean_object* v_cancelTk_x3f_563_; uint8_t v_suppressElabErrors_564_; lean_object* v_inheritedTraceOptions_565_; lean_object* v_ref_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
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
v_ref_566_ = l_Lean_replaceRef(v_ref_543_, v_ref_555_);
lean_inc_ref(v_inheritedTraceOptions_565_);
lean_inc(v_cancelTk_x3f_563_);
lean_inc(v_currMacroScope_561_);
lean_inc(v_quotContext_560_);
lean_inc(v_maxHeartbeats_559_);
lean_inc(v_initHeartbeats_558_);
lean_inc(v_openDecls_557_);
lean_inc(v_currNamespace_556_);
lean_inc(v_maxRecDepth_554_);
lean_inc(v_currRecDepth_553_);
lean_inc_ref(v_options_552_);
lean_inc_ref(v_fileMap_551_);
lean_inc_ref(v_fileName_550_);
v___x_567_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_567_, 0, v_fileName_550_);
lean_ctor_set(v___x_567_, 1, v_fileMap_551_);
lean_ctor_set(v___x_567_, 2, v_options_552_);
lean_ctor_set(v___x_567_, 3, v_currRecDepth_553_);
lean_ctor_set(v___x_567_, 4, v_maxRecDepth_554_);
lean_ctor_set(v___x_567_, 5, v_ref_566_);
lean_ctor_set(v___x_567_, 6, v_currNamespace_556_);
lean_ctor_set(v___x_567_, 7, v_openDecls_557_);
lean_ctor_set(v___x_567_, 8, v_initHeartbeats_558_);
lean_ctor_set(v___x_567_, 9, v_maxHeartbeats_559_);
lean_ctor_set(v___x_567_, 10, v_quotContext_560_);
lean_ctor_set(v___x_567_, 11, v_currMacroScope_561_);
lean_ctor_set(v___x_567_, 12, v_cancelTk_x3f_563_);
lean_ctor_set(v___x_567_, 13, v_inheritedTraceOptions_565_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*14, v_diag_562_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*14 + 1, v_suppressElabErrors_564_);
v___x_568_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_544_, v___y_545_, v___y_546_, v___x_567_, v___y_548_);
lean_dec_ref(v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object* v_ref_569_, lean_object* v_msg_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_569_, v_msg_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v_ref_569_);
return v_res_576_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__1(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__0));
v___x_579_ = l_Lean_stringToMessageData(v___x_578_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__3(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__2));
v___x_582_ = l_Lean_stringToMessageData(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__5(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__4));
v___x_585_ = l_Lean_stringToMessageData(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__9(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__8));
v___x_591_ = l_Lean_stringToMessageData(v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__12(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__11));
v___x_596_ = l_Lean_MessageData_ofFormat(v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object* v_funName_597_, lean_object* v_extraParams_598_, lean_object* v_tb_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
uint8_t v_synthetic_605_; 
v_synthetic_605_ = lean_ctor_get_uint8(v_tb_599_, sizeof(void*)*3 + 1);
if (v_synthetic_605_ == 0)
{
lean_object* v_ref_606_; lean_object* v_vars_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_ref_606_ = lean_ctor_get(v_tb_599_, 0);
v_vars_607_ = lean_ctor_get(v_tb_599_, 1);
v___x_608_ = lean_array_get_size(v_vars_607_);
v___x_609_ = lean_nat_dec_lt(v_extraParams_598_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v_extraParams_598_);
lean_dec(v_funName_597_);
v___x_610_ = lean_box(0);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_msg_622_; lean_object* v___x_623_; lean_object* v_ident_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_612_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_608_);
v___x_613_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__1, &l_Lean_Elab_TerminationBy_checkVars___closed__1_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__1);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
lean_inc(v_funName_597_);
v___x_615_ = l_Lean_MessageData_ofName(v_funName_597_);
v___x_616_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__3, &l_Lean_Elab_TerminationBy_checkVars___closed__3_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__3);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_598_);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__5, &l_Lean_Elab_TerminationBy_checkVars___closed__5_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__5);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v_msg_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_622_, 0, v___x_614_);
lean_ctor_set(v_msg_622_, 1, v___x_621_);
v___x_623_ = lean_unsigned_to_nat(0u);
v_ident_624_ = lean_array_fget_borrowed(v_vars_607_, v___x_623_);
v___x_625_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__7));
lean_inc(v_ident_624_);
v___x_626_ = l_Lean_Syntax_isOfKind(v_ident_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
lean_dec(v_funName_597_);
v___x_627_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_606_, v_msg_622_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = l_Lean_TSyntax_getId(v_ident_624_);
v___x_629_ = l_Lean_Name_isSuffixOf(v___x_628_, v_funName_597_);
lean_dec(v_funName_597_);
lean_dec(v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_606_, v_msg_622_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
return v___x_630_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_msg_634_; lean_object* v___x_635_; 
v___x_631_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__9, &l_Lean_Elab_TerminationBy_checkVars___closed__9_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__9);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v_msg_622_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__12, &l_Lean_Elab_TerminationBy_checkVars___closed__12_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__12);
v_msg_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_634_, 0, v___x_632_);
lean_ctor_set(v_msg_634_, 1, v___x_633_);
v___x_635_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_606_, v_msg_634_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
return v___x_635_;
}
}
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec(v_extraParams_598_);
lean_dec(v_funName_597_);
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object* v_funName_638_, lean_object* v_extraParams_639_, lean_object* v_tb_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_TerminationBy_checkVars(v_funName_638_, v_extraParams_639_, v_tb_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec_ref(v_tb_640_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_object* v_00_u03b1_647_, lean_object* v_ref_648_, lean_object* v_msg_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_648_, v_msg_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object* v_00_u03b1_656_, lean_object* v_ref_657_, lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(v_00_u03b1_656_, v_ref_657_, v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v_ref_657_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_object* v_00_u03b1_665_, lean_object* v_msg_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_673_, lean_object* v_msg_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_673_, v_msg_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object* v_val_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v_val_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object* v_stx_683_, lean_object* v_terminationBy_x3f_x3f_684_, lean_object* v_terminationBy_x3f_685_, lean_object* v_partialFixpoint_x3f_686_, lean_object* v___x_687_, lean_object* v_toPure_688_, lean_object* v_decreasingBy_x3f_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_690_, 0, v_stx_683_);
lean_ctor_set(v___x_690_, 1, v_terminationBy_x3f_x3f_684_);
lean_ctor_set(v___x_690_, 2, v_terminationBy_x3f_685_);
lean_ctor_set(v___x_690_, 3, v_partialFixpoint_x3f_686_);
lean_ctor_set(v___x_690_, 4, v_decreasingBy_x3f_689_);
lean_ctor_set(v___x_690_, 5, v___x_687_);
v___x_691_ = lean_apply_2(v_toPure_688_, lean_box(0), v___x_690_);
return v___x_691_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* v_stx_696_, lean_object* v_terminationBy_x3f_x3f_697_, lean_object* v_terminationBy_x3f_698_, lean_object* v___x_699_, lean_object* v_toPure_700_, lean_object* v_d_x3f_701_, lean_object* v_toBind_702_, lean_object* v_toFunctor_703_, lean_object* v___f_704_, lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v___x_710_, lean_object* v_partialFixpoint_x3f_711_){
_start:
{
lean_object* v___f_712_; 
lean_inc(v_toPure_700_);
v___f_712_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1), 7, 6);
lean_closure_set(v___f_712_, 0, v_stx_696_);
lean_closure_set(v___f_712_, 1, v_terminationBy_x3f_x3f_697_);
lean_closure_set(v___f_712_, 2, v_terminationBy_x3f_698_);
lean_closure_set(v___f_712_, 3, v_partialFixpoint_x3f_711_);
lean_closure_set(v___f_712_, 4, v___x_699_);
lean_closure_set(v___f_712_, 5, v_toPure_700_);
if (lean_obj_tag(v_d_x3f_701_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v___x_707_);
lean_dec_ref(v___x_706_);
lean_dec_ref(v___x_705_);
lean_dec_ref(v___f_704_);
lean_dec_ref(v_toFunctor_703_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_713_);
v___x_715_ = lean_apply_4(v_toBind_702_, lean_box(0), lean_box(0), v___x_714_, v___f_712_);
return v___x_715_;
}
else
{
lean_object* v_val_716_; lean_object* v_map_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_735_; 
v_val_716_ = lean_ctor_get(v_d_x3f_701_, 0);
lean_inc(v_val_716_);
lean_dec_ref(v_d_x3f_701_);
v_map_717_ = lean_ctor_get(v_toFunctor_703_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v_toFunctor_703_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v_toFunctor_703_, 1);
lean_dec(v_unused_736_);
v___x_719_ = v_toFunctor_703_;
v_isShared_720_ = v_isSharedCheck_735_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_map_717_);
lean_dec(v_toFunctor_703_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_735_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___y_722_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_725_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0));
v___x_726_ = l_Lean_Name_mkStr4(v___x_705_, v___x_706_, v___x_707_, v___x_725_);
lean_inc(v_val_716_);
v___x_727_ = l_Lean_Syntax_isOfKind(v_val_716_, v___x_726_);
lean_dec(v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_del_object(v___x_719_);
lean_dec(v_toPure_700_);
v___x_728_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2, &l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2);
v___x_729_ = l_Lean_throwErrorAt___redArg(v_inst_708_, v_inst_709_, v_val_716_, v___x_728_);
v___y_722_ = v___x_729_;
goto v___jp_721_;
}
else
{
lean_object* v_tactic_730_; lean_object* v___x_732_; 
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
v_tactic_730_ = l_Lean_Syntax_getArg(v_val_716_, v___x_710_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v_tactic_730_);
lean_ctor_set(v___x_719_, 0, v_val_716_);
v___x_732_ = v___x_719_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_val_716_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_tactic_730_);
v___x_732_ = v_reuseFailAlloc_734_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_732_);
v___y_722_ = v___x_733_;
goto v___jp_721_;
}
}
v___jp_721_:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_apply_4(v_map_717_, lean_box(0), lean_box(0), v___f_704_, v___y_722_);
v___x_724_ = lean_apply_4(v_toBind_702_, lean_box(0), lean_box(0), v___x_723_, v___f_712_);
return v___x_724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object* v_stx_737_, lean_object* v_terminationBy_x3f_x3f_738_, lean_object* v_terminationBy_x3f_739_, lean_object* v___x_740_, lean_object* v_toPure_741_, lean_object* v_d_x3f_742_, lean_object* v_toBind_743_, lean_object* v_toFunctor_744_, lean_object* v___f_745_, lean_object* v___x_746_, lean_object* v___x_747_, lean_object* v___x_748_, lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v___x_751_, lean_object* v_partialFixpoint_x3f_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_737_, v_terminationBy_x3f_x3f_738_, v_terminationBy_x3f_739_, v___x_740_, v_toPure_741_, v_d_x3f_742_, v_toBind_743_, v_toFunctor_744_, v___f_745_, v___x_746_, v___x_747_, v___x_748_, v_inst_749_, v_inst_750_, v___x_751_, v_partialFixpoint_x3f_752_);
lean_dec(v___x_751_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object* v_stx_760_, lean_object* v_terminationBy_x3f_x3f_761_, lean_object* v___x_762_, lean_object* v_toPure_763_, lean_object* v_d_x3f_764_, lean_object* v_toBind_765_, lean_object* v_toFunctor_766_, lean_object* v___f_767_, lean_object* v___x_768_, lean_object* v___x_769_, lean_object* v___x_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v___x_773_, lean_object* v_t_x3f_774_, lean_object* v_terminationBy_x3f_775_){
_start:
{
lean_object* v___f_776_; 
lean_inc(v___x_773_);
lean_inc_ref(v___x_770_);
lean_inc_ref(v___x_769_);
lean_inc_ref(v___x_768_);
lean_inc(v_toBind_765_);
lean_inc(v_toPure_763_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed), 16, 15);
lean_closure_set(v___f_776_, 0, v_stx_760_);
lean_closure_set(v___f_776_, 1, v_terminationBy_x3f_x3f_761_);
lean_closure_set(v___f_776_, 2, v_terminationBy_x3f_775_);
lean_closure_set(v___f_776_, 3, v___x_762_);
lean_closure_set(v___f_776_, 4, v_toPure_763_);
lean_closure_set(v___f_776_, 5, v_d_x3f_764_);
lean_closure_set(v___f_776_, 6, v_toBind_765_);
lean_closure_set(v___f_776_, 7, v_toFunctor_766_);
lean_closure_set(v___f_776_, 8, v___f_767_);
lean_closure_set(v___f_776_, 9, v___x_768_);
lean_closure_set(v___f_776_, 10, v___x_769_);
lean_closure_set(v___f_776_, 11, v___x_770_);
lean_closure_set(v___f_776_, 12, v_inst_771_);
lean_closure_set(v___f_776_, 13, v_inst_772_);
lean_closure_set(v___f_776_, 14, v___x_773_);
if (lean_obj_tag(v_t_x3f_774_) == 1)
{
lean_object* v_val_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_854_; 
v_val_777_ = lean_ctor_get(v_t_x3f_774_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_t_x3f_774_);
if (v_isSharedCheck_854_ == 0)
{
v___x_779_ = v_t_x3f_774_;
v_isShared_780_ = v_isSharedCheck_854_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_val_777_);
lean_dec(v_t_x3f_774_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_854_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_781_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_770_);
lean_inc_ref(v___x_769_);
lean_inc_ref(v___x_768_);
v___x_782_ = l_Lean_Name_mkStr4(v___x_768_, v___x_769_, v___x_770_, v___x_781_);
lean_inc(v_val_777_);
v___x_783_ = l_Lean_Syntax_isOfKind(v_val_777_, v___x_782_);
lean_dec(v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_784_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_770_);
lean_inc_ref(v___x_769_);
lean_inc_ref(v___x_768_);
v___x_785_ = l_Lean_Name_mkStr4(v___x_768_, v___x_769_, v___x_770_, v___x_784_);
lean_inc(v_val_777_);
v___x_786_ = l_Lean_Syntax_isOfKind(v_val_777_, v___x_785_);
lean_dec(v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_787_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_788_ = l_Lean_Name_mkStr4(v___x_768_, v___x_769_, v___x_770_, v___x_787_);
lean_inc(v_val_777_);
v___x_789_ = l_Lean_Syntax_isOfKind(v_val_777_, v___x_788_);
lean_dec(v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___f_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_del_object(v___x_779_);
lean_dec(v_val_777_);
lean_dec(v___x_773_);
v___f_790_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_790_, 0, v___f_776_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_791_);
v___x_793_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_792_, v___f_790_);
return v___x_793_;
}
else
{
lean_object* v___f_794_; lean_object* v_term_x3f_796_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___f_794_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_794_, 0, v___f_776_);
v___x_804_ = l_Lean_Syntax_getArg(v_val_777_, v___x_773_);
v___x_805_ = l_Lean_Syntax_isNone(v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_804_);
v___x_807_ = l_Lean_Syntax_matchesNull(v___x_804_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec(v___x_804_);
lean_del_object(v___x_779_);
lean_dec(v_val_777_);
lean_dec(v___x_773_);
v___x_808_ = lean_box(0);
v___x_809_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_808_);
v___x_810_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_809_, v___f_794_);
return v___x_810_;
}
else
{
lean_object* v_term_x3f_811_; lean_object* v___x_812_; 
v_term_x3f_811_ = l_Lean_Syntax_getArg(v___x_804_, v___x_773_);
lean_dec(v___x_773_);
lean_dec(v___x_804_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v_term_x3f_811_);
v_term_x3f_796_ = v___x_812_;
goto v___jp_795_;
}
}
else
{
lean_object* v___x_813_; 
lean_dec(v___x_804_);
lean_dec(v___x_773_);
v___x_813_ = lean_box(0);
v_term_x3f_796_ = v___x_813_;
goto v___jp_795_;
}
v___jp_795_:
{
uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_797_ = 2;
v___x_798_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_798_, 0, v_val_777_);
lean_ctor_set(v___x_798_, 1, v_term_x3f_796_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*2, v___x_797_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_798_);
v___x_800_ = v___x_779_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_803_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_800_);
v___x_802_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_801_, v___f_794_);
return v___x_802_;
}
}
}
}
else
{
lean_object* v___f_814_; lean_object* v_term_x3f_816_; lean_object* v___x_824_; uint8_t v___x_825_; 
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_769_);
lean_dec_ref(v___x_768_);
v___f_814_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_814_, 0, v___f_776_);
v___x_824_ = l_Lean_Syntax_getArg(v_val_777_, v___x_773_);
v___x_825_ = l_Lean_Syntax_isNone(v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_824_);
v___x_827_ = l_Lean_Syntax_matchesNull(v___x_824_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec(v___x_824_);
lean_del_object(v___x_779_);
lean_dec(v_val_777_);
lean_dec(v___x_773_);
v___x_828_ = lean_box(0);
v___x_829_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_828_);
v___x_830_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_829_, v___f_814_);
return v___x_830_;
}
else
{
lean_object* v_term_x3f_831_; lean_object* v___x_832_; 
v_term_x3f_831_ = l_Lean_Syntax_getArg(v___x_824_, v___x_773_);
lean_dec(v___x_773_);
lean_dec(v___x_824_);
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v_term_x3f_831_);
v_term_x3f_816_ = v___x_832_;
goto v___jp_815_;
}
}
else
{
lean_object* v___x_833_; 
lean_dec(v___x_824_);
lean_dec(v___x_773_);
v___x_833_ = lean_box(0);
v_term_x3f_816_ = v___x_833_;
goto v___jp_815_;
}
v___jp_815_:
{
uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_817_ = 1;
v___x_818_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_818_, 0, v_val_777_);
lean_ctor_set(v___x_818_, 1, v_term_x3f_816_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*2, v___x_817_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_818_);
v___x_820_ = v___x_779_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_823_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_820_);
v___x_822_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_821_, v___f_814_);
return v___x_822_;
}
}
}
}
else
{
lean_object* v___f_834_; lean_object* v_term_x3f_836_; lean_object* v___x_844_; uint8_t v___x_845_; 
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_769_);
lean_dec_ref(v___x_768_);
v___f_834_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_834_, 0, v___f_776_);
v___x_844_ = l_Lean_Syntax_getArg(v_val_777_, v___x_773_);
v___x_845_ = l_Lean_Syntax_isNone(v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_844_);
v___x_847_ = l_Lean_Syntax_matchesNull(v___x_844_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v___x_844_);
lean_del_object(v___x_779_);
lean_dec(v_val_777_);
lean_dec(v___x_773_);
v___x_848_ = lean_box(0);
v___x_849_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_848_);
v___x_850_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_849_, v___f_834_);
return v___x_850_;
}
else
{
lean_object* v_term_x3f_851_; lean_object* v___x_852_; 
v_term_x3f_851_ = l_Lean_Syntax_getArg(v___x_844_, v___x_773_);
lean_dec(v___x_773_);
lean_dec(v___x_844_);
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v_term_x3f_851_);
v_term_x3f_836_ = v___x_852_;
goto v___jp_835_;
}
}
else
{
lean_object* v___x_853_; 
lean_dec(v___x_844_);
lean_dec(v___x_773_);
v___x_853_ = lean_box(0);
v_term_x3f_836_ = v___x_853_;
goto v___jp_835_;
}
v___jp_835_:
{
uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_837_ = 0;
v___x_838_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_838_, 0, v_val_777_);
lean_ctor_set(v___x_838_, 1, v_term_x3f_836_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*2, v___x_837_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_838_);
v___x_840_ = v___x_779_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_843_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_840_);
v___x_842_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_841_, v___f_834_);
return v___x_842_;
}
}
}
}
}
else
{
lean_object* v___f_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec(v_t_x3f_774_);
lean_dec(v___x_773_);
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_769_);
lean_dec_ref(v___x_768_);
v___f_855_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_855_, 0, v___f_776_);
v___x_856_ = lean_box(0);
v___x_857_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_856_);
v___x_858_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_857_, v___f_855_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* v___f_859_, lean_object* v_terminationBy_x3f_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = lean_apply_1(v___f_859_, v_terminationBy_x3f_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2));
v___x_866_ = l_Lean_stringToMessageData(v___x_865_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4));
v___x_869_ = l_Lean_stringToMessageData(v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* v_stx_870_, lean_object* v___x_871_, lean_object* v_toPure_872_, lean_object* v_d_x3f_873_, lean_object* v_toBind_874_, lean_object* v_toFunctor_875_, lean_object* v___f_876_, lean_object* v___x_877_, lean_object* v___x_878_, lean_object* v___x_879_, lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v___x_882_, lean_object* v_t_x3f_883_, lean_object* v_terminationBy_x3f_x3f_884_){
_start:
{
lean_object* v___f_885_; 
lean_inc(v_t_x3f_883_);
lean_inc(v___x_882_);
lean_inc_ref(v_inst_881_);
lean_inc_ref(v_inst_880_);
lean_inc_ref(v___x_879_);
lean_inc_ref(v___x_878_);
lean_inc_ref(v___x_877_);
lean_inc(v_toBind_874_);
lean_inc(v_toPure_872_);
lean_inc(v___x_871_);
v___f_885_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11), 16, 15);
lean_closure_set(v___f_885_, 0, v_stx_870_);
lean_closure_set(v___f_885_, 1, v_terminationBy_x3f_x3f_884_);
lean_closure_set(v___f_885_, 2, v___x_871_);
lean_closure_set(v___f_885_, 3, v_toPure_872_);
lean_closure_set(v___f_885_, 4, v_d_x3f_873_);
lean_closure_set(v___f_885_, 5, v_toBind_874_);
lean_closure_set(v___f_885_, 6, v_toFunctor_875_);
lean_closure_set(v___f_885_, 7, v___f_876_);
lean_closure_set(v___f_885_, 8, v___x_877_);
lean_closure_set(v___f_885_, 9, v___x_878_);
lean_closure_set(v___f_885_, 10, v___x_879_);
lean_closure_set(v___f_885_, 11, v_inst_880_);
lean_closure_set(v___f_885_, 12, v_inst_881_);
lean_closure_set(v___f_885_, 13, v___x_882_);
lean_closure_set(v___f_885_, 14, v_t_x3f_883_);
if (lean_obj_tag(v_t_x3f_883_) == 1)
{
lean_object* v_val_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_998_; 
v_val_886_ = lean_ctor_get(v_t_x3f_883_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v_t_x3f_883_);
if (v_isSharedCheck_998_ == 0)
{
v___x_888_ = v_t_x3f_883_;
v_isShared_889_ = v_isSharedCheck_998_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_val_886_);
lean_dec(v_t_x3f_883_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_998_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_890_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0));
lean_inc_ref(v___x_879_);
lean_inc_ref(v___x_878_);
lean_inc_ref(v___x_877_);
v___x_891_ = l_Lean_Name_mkStr4(v___x_877_, v___x_878_, v___x_879_, v___x_890_);
lean_inc(v_val_886_);
v___x_892_ = l_Lean_Syntax_isOfKind(v_val_886_, v___x_891_);
lean_dec(v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
lean_del_object(v___x_888_);
lean_dec(v___x_871_);
v___x_893_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1));
lean_inc_ref(v___x_879_);
lean_inc_ref(v___x_878_);
lean_inc_ref(v___x_877_);
v___x_894_ = l_Lean_Name_mkStr4(v___x_877_, v___x_878_, v___x_879_, v___x_893_);
lean_inc(v_val_886_);
v___x_895_ = l_Lean_Syntax_isOfKind(v_val_886_, v___x_894_);
lean_dec(v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_896_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_879_);
lean_inc_ref(v___x_878_);
lean_inc_ref(v___x_877_);
v___x_897_ = l_Lean_Name_mkStr4(v___x_877_, v___x_878_, v___x_879_, v___x_896_);
lean_inc(v_val_886_);
v___x_898_ = l_Lean_Syntax_isOfKind(v_val_886_, v___x_897_);
lean_dec(v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_899_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_879_);
lean_inc_ref(v___x_878_);
lean_inc_ref(v___x_877_);
v___x_900_ = l_Lean_Name_mkStr4(v___x_877_, v___x_878_, v___x_879_, v___x_899_);
lean_inc(v_val_886_);
v___x_901_ = l_Lean_Syntax_isOfKind(v_val_886_, v___x_900_);
lean_dec(v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_903_ = l_Lean_Name_mkStr4(v___x_877_, v___x_878_, v___x_879_, v___x_902_);
lean_inc(v_val_886_);
v___x_904_ = l_Lean_Syntax_isOfKind(v_val_886_, v___x_903_);
lean_dec(v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___f_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec(v___x_882_);
lean_dec(v_toPure_872_);
v___f_905_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_905_, 0, v___f_885_);
v___x_906_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_907_ = l_Lean_throwErrorAt___redArg(v_inst_880_, v_inst_881_, v_val_886_, v___x_906_);
v___x_908_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_907_, v___f_905_);
return v___x_908_;
}
else
{
lean_object* v___f_909_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___f_909_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_909_, 0, v___f_885_);
v___x_914_ = l_Lean_Syntax_getArg(v_val_886_, v___x_882_);
lean_dec(v___x_882_);
v___x_915_ = l_Lean_Syntax_isNone(v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_unsigned_to_nat(2u);
v___x_917_ = l_Lean_Syntax_matchesNull(v___x_914_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_toPure_872_);
v___x_918_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_919_ = l_Lean_throwErrorAt___redArg(v_inst_880_, v_inst_881_, v_val_886_, v___x_918_);
v___x_920_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_919_, v___f_909_);
return v___x_920_;
}
else
{
lean_dec(v_val_886_);
lean_dec_ref(v_inst_881_);
lean_dec_ref(v_inst_880_);
goto v___jp_910_;
}
}
else
{
lean_dec(v___x_914_);
lean_dec(v_val_886_);
lean_dec_ref(v_inst_881_);
lean_dec_ref(v_inst_880_);
goto v___jp_910_;
}
v___jp_910_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = lean_box(0);
v___x_912_ = lean_apply_2(v_toPure_872_, lean_box(0), v___x_911_);
v___x_913_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_912_, v___f_909_);
return v___x_913_;
}
}
}
else
{
lean_object* v___f_921_; lean_object* v___x_926_; uint8_t v___x_927_; 
lean_dec_ref(v___x_879_);
lean_dec_ref(v___x_878_);
lean_dec_ref(v___x_877_);
v___f_921_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_921_, 0, v___f_885_);
v___x_926_ = l_Lean_Syntax_getArg(v_val_886_, v___x_882_);
lean_dec(v___x_882_);
v___x_927_ = l_Lean_Syntax_isNone(v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = lean_unsigned_to_nat(2u);
v___x_929_ = l_Lean_Syntax_matchesNull(v___x_926_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_toPure_872_);
v___x_930_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_931_ = l_Lean_throwErrorAt___redArg(v_inst_880_, v_inst_881_, v_val_886_, v___x_930_);
v___x_932_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_931_, v___f_921_);
return v___x_932_;
}
else
{
lean_dec(v_val_886_);
lean_dec_ref(v_inst_881_);
lean_dec_ref(v_inst_880_);
goto v___jp_922_;
}
}
else
{
lean_dec(v___x_926_);
lean_dec(v_val_886_);
lean_dec_ref(v_inst_881_);
lean_dec_ref(v_inst_880_);
goto v___jp_922_;
}
v___jp_922_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = lean_box(0);
v___x_924_ = lean_apply_2(v_toPure_872_, lean_box(0), v___x_923_);
v___x_925_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_924_, v___f_921_);
return v___x_925_;
}
}
}
else
{
lean_object* v___f_933_; lean_object* v___x_938_; uint8_t v___x_939_; 
lean_dec_ref(v___x_879_);
lean_dec_ref(v___x_878_);
lean_dec_ref(v___x_877_);
v___f_933_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_933_, 0, v___f_885_);
v___x_938_ = l_Lean_Syntax_getArg(v_val_886_, v___x_882_);
lean_dec(v___x_882_);
v___x_939_ = l_Lean_Syntax_isNone(v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_unsigned_to_nat(2u);
v___x_941_ = l_Lean_Syntax_matchesNull(v___x_938_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec(v_toPure_872_);
v___x_942_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_943_ = l_Lean_throwErrorAt___redArg(v_inst_880_, v_inst_881_, v_val_886_, v___x_942_);
v___x_944_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_943_, v___f_933_);
return v___x_944_;
}
else
{
lean_dec(v_val_886_);
lean_dec_ref(v_inst_881_);
lean_dec_ref(v_inst_880_);
goto v___jp_934_;
}
}
else
{
lean_dec(v___x_938_);
lean_dec(v_val_886_);
lean_dec_ref(v_inst_881_);
lean_dec_ref(v_inst_880_);
goto v___jp_934_;
}
v___jp_934_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_box(0);
v___x_936_ = lean_apply_2(v_toPure_872_, lean_box(0), v___x_935_);
v___x_937_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_936_, v___f_933_);
return v___x_937_;
}
}
}
else
{
lean_object* v___f_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec(v_val_886_);
lean_dec(v___x_882_);
lean_dec_ref(v_inst_881_);
lean_dec_ref(v_inst_880_);
lean_dec_ref(v___x_879_);
lean_dec_ref(v___x_878_);
lean_dec_ref(v___x_877_);
v___f_945_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_945_, 0, v___f_885_);
v___x_946_ = lean_box(0);
v___x_947_ = lean_apply_2(v_toPure_872_, lean_box(0), v___x_946_);
v___x_948_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_947_, v___f_945_);
return v___x_948_;
}
}
else
{
lean_object* v___f_949_; uint8_t v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; uint8_t v___y_954_; lean_object* v___y_962_; uint8_t v___y_963_; uint8_t v___y_964_; lean_object* v_s_971_; lean_object* v___x_989_; uint8_t v___x_990_; 
lean_dec_ref(v___x_879_);
lean_dec_ref(v___x_878_);
lean_dec_ref(v___x_877_);
v___f_949_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_949_, 0, v___f_885_);
v___x_989_ = l_Lean_Syntax_getArg(v_val_886_, v___x_882_);
v___x_990_ = l_Lean_Syntax_isNone(v___x_989_);
if (v___x_990_ == 0)
{
uint8_t v___x_991_; 
lean_inc(v___x_989_);
v___x_991_ = l_Lean_Syntax_matchesNull(v___x_989_, v___x_882_);
lean_dec(v___x_882_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec(v___x_989_);
lean_del_object(v___x_888_);
lean_dec(v_toPure_872_);
lean_dec(v___x_871_);
v___x_992_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_993_ = l_Lean_throwErrorAt___redArg(v_inst_880_, v_inst_881_, v_val_886_, v___x_992_);
v___x_994_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_993_, v___f_949_);
return v___x_994_;
}
else
{
lean_object* v_s_995_; lean_object* v___x_996_; 
v_s_995_ = l_Lean_Syntax_getArg(v___x_989_, v___x_871_);
lean_dec(v___x_989_);
v___x_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_996_, 0, v_s_995_);
v_s_971_ = v___x_996_;
goto v___jp_970_;
}
}
else
{
lean_object* v___x_997_; 
lean_dec(v___x_989_);
lean_dec(v___x_882_);
v___x_997_ = lean_box(0);
v_s_971_ = v___x_997_;
goto v___jp_970_;
}
v___jp_950_:
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_955_, 0, v_val_886_);
lean_ctor_set(v___x_955_, 1, v___y_953_);
lean_ctor_set(v___x_955_, 2, v___y_952_);
lean_ctor_set_uint8(v___x_955_, sizeof(void*)*3, v___y_954_);
lean_ctor_set_uint8(v___x_955_, sizeof(void*)*3 + 1, v___y_951_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_955_);
v___x_957_ = v___x_888_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_960_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_apply_2(v_toPure_872_, lean_box(0), v___x_957_);
v___x_959_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_958_, v___f_949_);
return v___x_959_;
}
}
v___jp_961_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_965_ = lean_mk_empty_array_with_capacity(v___x_871_);
lean_dec(v___x_871_);
v___x_966_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_966_, 0, v_val_886_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
lean_ctor_set(v___x_966_, 2, v___y_962_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*3, v___y_964_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*3 + 1, v___y_963_);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
v___x_968_ = lean_apply_2(v_toPure_872_, lean_box(0), v___x_967_);
v___x_969_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_968_, v___f_949_);
return v___x_969_;
}
v___jp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_972_ = lean_unsigned_to_nat(2u);
v___x_973_ = l_Lean_Syntax_getArg(v_val_886_, v___x_972_);
lean_inc(v___x_973_);
v___x_974_ = l_Lean_Syntax_matchesNull(v___x_973_, v___x_972_);
if (v___x_974_ == 0)
{
uint8_t v___x_975_; 
lean_del_object(v___x_888_);
v___x_975_ = l_Lean_Syntax_matchesNull(v___x_973_, v___x_871_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec(v_s_971_);
lean_dec(v_toPure_872_);
lean_dec(v___x_871_);
v___x_976_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_977_ = l_Lean_throwErrorAt___redArg(v_inst_880_, v_inst_881_, v_val_886_, v___x_976_);
v___x_978_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_977_, v___f_949_);
return v___x_978_;
}
else
{
lean_object* v___x_979_; lean_object* v_body_980_; 
lean_dec_ref(v_inst_881_);
lean_dec_ref(v_inst_880_);
v___x_979_ = lean_unsigned_to_nat(3u);
v_body_980_ = l_Lean_Syntax_getArg(v_val_886_, v___x_979_);
if (lean_obj_tag(v_s_971_) == 0)
{
v___y_962_ = v_body_980_;
v___y_963_ = v___x_974_;
v___y_964_ = v___x_974_;
goto v___jp_961_;
}
else
{
lean_dec_ref(v_s_971_);
v___y_962_ = v_body_980_;
v___y_963_ = v___x_974_;
v___y_964_ = v___x_975_;
goto v___jp_961_;
}
}
}
else
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = l_Lean_Syntax_getArg(v___x_973_, v___x_871_);
lean_dec(v___x_973_);
lean_inc(v___x_981_);
v___x_982_ = l_Lean_Syntax_matchesNull(v___x_981_, v___x_871_);
lean_dec(v___x_871_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v_body_984_; lean_object* v_vars_985_; 
lean_dec_ref(v_inst_881_);
lean_dec_ref(v_inst_880_);
v___x_983_ = lean_unsigned_to_nat(3u);
v_body_984_ = l_Lean_Syntax_getArg(v_val_886_, v___x_983_);
v_vars_985_ = l_Lean_Syntax_getArgs(v___x_981_);
lean_dec(v___x_981_);
if (lean_obj_tag(v_s_971_) == 0)
{
v___y_951_ = v___x_982_;
v___y_952_ = v_body_984_;
v___y_953_ = v_vars_985_;
v___y_954_ = v___x_982_;
goto v___jp_950_;
}
else
{
lean_dec_ref(v_s_971_);
v___y_951_ = v___x_982_;
v___y_952_ = v_body_984_;
v___y_953_ = v_vars_985_;
v___y_954_ = v___x_974_;
goto v___jp_950_;
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec(v___x_981_);
lean_dec(v_s_971_);
lean_del_object(v___x_888_);
lean_dec(v_toPure_872_);
v___x_986_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
v___x_987_ = l_Lean_throwErrorAt___redArg(v_inst_880_, v_inst_881_, v_val_886_, v___x_986_);
v___x_988_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_987_, v___f_949_);
return v___x_988_;
}
}
}
}
}
}
else
{
lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec(v_t_x3f_883_);
lean_dec(v___x_882_);
lean_dec_ref(v_inst_881_);
lean_dec_ref(v_inst_880_);
lean_dec_ref(v___x_879_);
lean_dec_ref(v___x_878_);
lean_dec_ref(v___x_877_);
lean_dec(v___x_871_);
v___f_999_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_999_, 0, v___f_885_);
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_apply_2(v_toPure_872_, lean_box(0), v___x_1000_);
v___x_1002_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_1001_, v___f_999_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* v___f_1003_, lean_object* v_terminationBy_x3f_x3f_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_apply_1(v___f_1003_, v_terminationBy_x3f_x3f_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_stx_1030_){
_start:
{
if (lean_obj_tag(v_stx_1030_) == 0)
{
lean_object* v_toApplicative_1031_; lean_object* v_toPure_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_toApplicative_1031_ = lean_ctor_get(v_inst_1028_, 0);
lean_inc_ref(v_toApplicative_1031_);
lean_dec_ref(v_inst_1029_);
lean_dec_ref(v_inst_1028_);
v_toPure_1032_ = lean_ctor_get(v_toApplicative_1031_, 1);
lean_inc(v_toPure_1032_);
lean_dec_ref(v_toApplicative_1031_);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1035_, 0, v_stx_1030_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
lean_ctor_set(v___x_1035_, 2, v___x_1034_);
lean_ctor_set(v___x_1035_, 3, v___x_1034_);
lean_ctor_set(v___x_1035_, 4, v___x_1034_);
lean_ctor_set(v___x_1035_, 5, v___x_1033_);
v___x_1036_ = lean_apply_2(v_toPure_1032_, lean_box(0), v___x_1035_);
return v___x_1036_;
}
else
{
lean_object* v_toApplicative_1037_; lean_object* v_toBind_1038_; lean_object* v_toFunctor_1039_; lean_object* v_toPure_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_toApplicative_1037_ = lean_ctor_get(v_inst_1028_, 0);
v_toBind_1038_ = lean_ctor_get(v_inst_1028_, 1);
v_toFunctor_1039_ = lean_ctor_get(v_toApplicative_1037_, 0);
v_toPure_1040_ = lean_ctor_get(v_toApplicative_1037_, 1);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__0));
v___x_1042_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__1));
v___x_1043_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__2));
v___x_1044_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__4));
lean_inc(v_stx_1030_);
v___x_1045_ = l_Lean_Syntax_isOfKind(v_stx_1030_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1046_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1047_ = lean_box(0);
lean_inc_n(v_stx_1030_, 2);
v___x_1048_ = l_Lean_Syntax_formatStx(v_stx_1030_, v___x_1047_, v___x_1045_);
v___x_1049_ = l_Std_Format_defWidth;
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = l_Std_Format_pretty(v___x_1048_, v___x_1049_, v___x_1050_, v___x_1050_);
v___x_1052_ = lean_string_append(v___x_1046_, v___x_1051_);
lean_dec_ref(v___x_1051_);
v___x_1053_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
v___x_1055_ = l_Lean_Syntax_getKind(v_stx_1030_);
v___x_1056_ = 1;
v___x_1057_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1055_, v___x_1056_);
v___x_1058_ = lean_string_append(v___x_1054_, v___x_1057_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
v___x_1060_ = l_Lean_MessageData_ofFormat(v___x_1059_);
v___x_1061_ = l_Lean_throwErrorAt___redArg(v_inst_1028_, v_inst_1029_, v_stx_1030_, v___x_1060_);
return v___x_1061_;
}
else
{
lean_object* v___f_1062_; lean_object* v___x_1063_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v_d_x3f_1067_; lean_object* v_t_x3f_1091_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___f_1062_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__7));
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1129_ = l_Lean_Syntax_getArg(v_stx_1030_, v___x_1063_);
v___x_1130_ = l_Lean_Syntax_isNone(v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1129_);
v___x_1132_ = l_Lean_Syntax_matchesNull(v___x_1129_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec(v___x_1129_);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1134_ = lean_box(0);
lean_inc_n(v_stx_1030_, 2);
v___x_1135_ = l_Lean_Syntax_formatStx(v_stx_1030_, v___x_1134_, v___x_1132_);
v___x_1136_ = l_Std_Format_defWidth;
v___x_1137_ = l_Std_Format_pretty(v___x_1135_, v___x_1136_, v___x_1063_, v___x_1063_);
v___x_1138_ = lean_string_append(v___x_1133_, v___x_1137_);
lean_dec_ref(v___x_1137_);
v___x_1139_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1140_ = lean_string_append(v___x_1138_, v___x_1139_);
v___x_1141_ = l_Lean_Syntax_getKind(v_stx_1030_);
v___x_1142_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1141_, v___x_1045_);
v___x_1143_ = lean_string_append(v___x_1140_, v___x_1142_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
v___x_1145_ = l_Lean_MessageData_ofFormat(v___x_1144_);
v___x_1146_ = l_Lean_throwErrorAt___redArg(v_inst_1028_, v_inst_1029_, v_stx_1030_, v___x_1145_);
return v___x_1146_;
}
else
{
lean_object* v_t_x3f_1147_; lean_object* v___x_1148_; 
v_t_x3f_1147_ = l_Lean_Syntax_getArg(v___x_1129_, v___x_1063_);
lean_dec(v___x_1129_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_t_x3f_1147_);
v_t_x3f_1091_ = v___x_1148_;
goto v___jp_1090_;
}
}
else
{
lean_object* v___x_1149_; 
lean_dec(v___x_1129_);
v___x_1149_ = lean_box(0);
v_t_x3f_1091_ = v___x_1149_;
goto v___jp_1090_;
}
v___jp_1064_:
{
lean_object* v___f_1068_; 
lean_inc(v___y_1065_);
lean_inc(v_toBind_1038_);
lean_inc(v_toPure_1040_);
v___f_1068_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19), 15, 14);
lean_closure_set(v___f_1068_, 0, v_stx_1030_);
lean_closure_set(v___f_1068_, 1, v___x_1063_);
lean_closure_set(v___f_1068_, 2, v_toPure_1040_);
lean_closure_set(v___f_1068_, 3, v_d_x3f_1067_);
lean_closure_set(v___f_1068_, 4, v_toBind_1038_);
lean_closure_set(v___f_1068_, 5, v_toFunctor_1039_);
lean_closure_set(v___f_1068_, 6, v___f_1062_);
lean_closure_set(v___f_1068_, 7, v___x_1041_);
lean_closure_set(v___f_1068_, 8, v___x_1042_);
lean_closure_set(v___f_1068_, 9, v___x_1043_);
lean_closure_set(v___f_1068_, 10, v_inst_1028_);
lean_closure_set(v___f_1068_, 11, v_inst_1029_);
lean_closure_set(v___f_1068_, 12, v___y_1066_);
lean_closure_set(v___f_1068_, 13, v___y_1065_);
if (lean_obj_tag(v___y_1065_) == 1)
{
lean_object* v_val_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1085_; 
v_val_1069_ = lean_ctor_get(v___y_1065_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___y_1065_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1071_ = v___y_1065_;
v_isShared_1072_ = v_isSharedCheck_1085_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_val_1069_);
lean_dec(v___y_1065_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1085_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__8));
lean_inc(v_val_1069_);
v___x_1074_ = l_Lean_Syntax_isOfKind(v_val_1069_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_del_object(v___x_1071_);
lean_dec(v_val_1069_);
v___f_1075_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1075_, 0, v___f_1068_);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_apply_2(v_toPure_1040_, lean_box(0), v___x_1076_);
v___x_1078_ = lean_apply_4(v_toBind_1038_, lean_box(0), lean_box(0), v___x_1077_, v___f_1075_);
return v___x_1078_;
}
else
{
lean_object* v___f_1079_; lean_object* v___x_1081_; 
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1079_, 0, v___f_1068_);
if (v_isShared_1072_ == 0)
{
v___x_1081_ = v___x_1071_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_val_1069_);
v___x_1081_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_apply_2(v_toPure_1040_, lean_box(0), v___x_1081_);
v___x_1083_ = lean_apply_4(v_toBind_1038_, lean_box(0), lean_box(0), v___x_1082_, v___f_1079_);
return v___x_1083_;
}
}
}
}
else
{
lean_object* v___f_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec(v___y_1065_);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1086_, 0, v___f_1068_);
v___x_1087_ = lean_box(0);
v___x_1088_ = lean_apply_2(v_toPure_1040_, lean_box(0), v___x_1087_);
v___x_1089_ = lean_apply_4(v_toBind_1038_, lean_box(0), lean_box(0), v___x_1088_, v___f_1086_);
return v___x_1089_;
}
}
v___jp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = l_Lean_Syntax_getArg(v_stx_1030_, v___x_1092_);
v___x_1094_ = l_Lean_Syntax_isNone(v___x_1093_);
if (v___x_1094_ == 0)
{
uint8_t v___x_1095_; 
lean_inc(v___x_1093_);
v___x_1095_ = l_Lean_Syntax_matchesNull(v___x_1093_, v___x_1092_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec(v___x_1093_);
lean_dec(v_t_x3f_1091_);
v___x_1096_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1097_ = lean_box(0);
lean_inc_n(v_stx_1030_, 2);
v___x_1098_ = l_Lean_Syntax_formatStx(v_stx_1030_, v___x_1097_, v___x_1095_);
v___x_1099_ = l_Std_Format_defWidth;
v___x_1100_ = l_Std_Format_pretty(v___x_1098_, v___x_1099_, v___x_1063_, v___x_1063_);
v___x_1101_ = lean_string_append(v___x_1096_, v___x_1100_);
lean_dec_ref(v___x_1100_);
v___x_1102_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1103_ = lean_string_append(v___x_1101_, v___x_1102_);
v___x_1104_ = l_Lean_Syntax_getKind(v_stx_1030_);
v___x_1105_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1104_, v___x_1045_);
v___x_1106_ = lean_string_append(v___x_1103_, v___x_1105_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
v___x_1108_ = l_Lean_MessageData_ofFormat(v___x_1107_);
v___x_1109_ = l_Lean_throwErrorAt___redArg(v_inst_1028_, v_inst_1029_, v_stx_1030_, v___x_1108_);
return v___x_1109_;
}
else
{
lean_object* v_d_x3f_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v_d_x3f_1110_ = l_Lean_Syntax_getArg(v___x_1093_, v___x_1063_);
lean_dec(v___x_1093_);
v___x_1111_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__9));
lean_inc(v_d_x3f_1110_);
v___x_1112_ = l_Lean_Syntax_isOfKind(v_d_x3f_1110_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v_d_x3f_1110_);
lean_dec(v_t_x3f_1091_);
v___x_1113_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1114_ = lean_box(0);
lean_inc_n(v_stx_1030_, 2);
v___x_1115_ = l_Lean_Syntax_formatStx(v_stx_1030_, v___x_1114_, v___x_1112_);
v___x_1116_ = l_Std_Format_defWidth;
v___x_1117_ = l_Std_Format_pretty(v___x_1115_, v___x_1116_, v___x_1063_, v___x_1063_);
v___x_1118_ = lean_string_append(v___x_1113_, v___x_1117_);
lean_dec_ref(v___x_1117_);
v___x_1119_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1120_ = lean_string_append(v___x_1118_, v___x_1119_);
v___x_1121_ = l_Lean_Syntax_getKind(v_stx_1030_);
v___x_1122_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1121_, v___x_1095_);
v___x_1123_ = lean_string_append(v___x_1120_, v___x_1122_);
lean_dec_ref(v___x_1122_);
v___x_1124_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
v___x_1125_ = l_Lean_MessageData_ofFormat(v___x_1124_);
v___x_1126_ = l_Lean_throwErrorAt___redArg(v_inst_1028_, v_inst_1029_, v_stx_1030_, v___x_1125_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; 
lean_inc(v_toPure_1040_);
lean_inc_ref(v_toFunctor_1039_);
lean_inc(v_toBind_1038_);
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_d_x3f_1110_);
v___y_1065_ = v_t_x3f_1091_;
v___y_1066_ = v___x_1092_;
v_d_x3f_1067_ = v___x_1127_;
goto v___jp_1064_;
}
}
}
else
{
lean_object* v___x_1128_; 
lean_inc(v_toPure_1040_);
lean_inc_ref(v_toFunctor_1039_);
lean_inc(v_toBind_1038_);
lean_dec(v___x_1093_);
v___x_1128_ = lean_box(0);
v___y_1065_ = v_t_x3f_1091_;
v___y_1066_ = v___x_1092_;
v_d_x3f_1067_ = v___x_1128_;
goto v___jp_1064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* v_m_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_stx_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Elab_elabTerminationHints___redArg(v_inst_1151_, v_inst_1152_, v_stx_1153_);
return v___x_1154_;
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
