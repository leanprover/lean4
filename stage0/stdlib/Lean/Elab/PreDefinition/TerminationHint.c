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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, uint8_t v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_inc(v_k_27_);
return v_k_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_ctorElim___boxed(lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Elab_PartialFixpointType_ctorElim(v_motive_28_, v_ctorIdx_29_, v_t_boxed_33_, v_h_31_, v_k_32_);
lean_dec(v_k_32_);
lean_dec(v_ctorIdx_29_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(lean_object* v_partialFixpoint_35_){
_start:
{
lean_inc(v_partialFixpoint_35_);
return v_partialFixpoint_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg___boxed(lean_object* v_partialFixpoint_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(v_partialFixpoint_36_);
lean_dec(v_partialFixpoint_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_partialFixpoint_41_){
_start:
{
lean_inc(v_partialFixpoint_41_);
return v_partialFixpoint_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_partialFixpoint_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_partialFixpoint_45_);
lean_dec(v_partialFixpoint_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(lean_object* v_coinductiveFixpoint_48_){
_start:
{
lean_inc(v_coinductiveFixpoint_48_);
return v_coinductiveFixpoint_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg___boxed(lean_object* v_coinductiveFixpoint_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(v_coinductiveFixpoint_49_);
lean_dec(v_coinductiveFixpoint_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_coinductiveFixpoint_54_){
_start:
{
lean_inc(v_coinductiveFixpoint_54_);
return v_coinductiveFixpoint_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_coinductiveFixpoint_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_coinductiveFixpoint_58_);
lean_dec(v_coinductiveFixpoint_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(lean_object* v_inductiveFixpoint_61_){
_start:
{
lean_inc(v_inductiveFixpoint_61_);
return v_inductiveFixpoint_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg___boxed(lean_object* v_inductiveFixpoint_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(v_inductiveFixpoint_62_);
lean_dec(v_inductiveFixpoint_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_inductiveFixpoint_67_){
_start:
{
lean_inc(v_inductiveFixpoint_67_);
return v_inductiveFixpoint_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_inductiveFixpoint_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_inductiveFixpoint_71_);
lean_dec(v_inductiveFixpoint_71_);
return v_res_73_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedPartialFixpointType_default(void){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = 0;
return v___x_74_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedPartialFixpointType(void){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
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
uint8_t v_x_21__boxed_92_; uint8_t v_res_93_; lean_object* v_r_94_; 
v_x_21__boxed_92_ = lean_unbox(v_x_91_);
v_res_93_ = l_Lean_Elab_isInductiveFixpoint(v_x_21__boxed_92_);
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
uint8_t v_x_21__boxed_99_; uint8_t v_res_100_; lean_object* v_r_101_; 
v_x_21__boxed_99_ = lean_unbox(v_x_98_);
v_res_100_ = l_Lean_Elab_isCoinductiveFixpoint(v_x_21__boxed_99_);
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
uint8_t v_x_21__boxed_106_; uint8_t v_res_107_; lean_object* v_r_108_; 
v_x_21__boxed_106_ = lean_unbox(v_x_105_);
v_res_107_ = l_Lean_Elab_isPartialFixpoint(v_x_21__boxed_106_);
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
v___x_117_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
lean_ctor_set(v___x_122_, 2, v___x_121_);
lean_ctor_set(v___x_122_, 3, v___x_121_);
lean_ctor_set(v___x_122_, 4, v___x_120_);
lean_ctor_set(v___x_122_, 5, v___x_120_);
lean_ctor_set(v___x_122_, 6, v___x_120_);
lean_ctor_set(v___x_122_, 7, v___x_120_);
lean_ctor_set(v___x_122_, 8, v___x_120_);
lean_ctor_set(v___x_122_, 9, v___x_120_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = lean_unsigned_to_nat(32u);
v___x_124_ = lean_mk_empty_array_with_capacity(v___x_123_);
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_126_ = ((size_t)5ULL);
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_unsigned_to_nat(32u);
v___x_129_ = lean_mk_empty_array_with_capacity(v___x_128_);
v___x_130_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3);
v___x_131_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
lean_ctor_set(v___x_131_, 2, v___x_127_);
lean_ctor_set(v___x_131_, 3, v___x_127_);
lean_ctor_set_usize(v___x_131_, 4, v___x_126_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_132_ = lean_box(1);
v___x_133_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4);
v___x_134_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
v___x_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_133_);
lean_ctor_set(v___x_135_, 2, v___x_132_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(lean_object* v_msgData_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___x_140_; lean_object* v_env_141_; lean_object* v_options_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_140_ = lean_st_ref_get(v___y_138_);
v_env_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc_ref(v_env_141_);
lean_dec(v___x_140_);
v_options_142_ = lean_ctor_get(v___y_137_, 2);
v___x_143_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2);
v___x_144_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_142_);
v___x_145_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_145_, 0, v_env_141_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
lean_ctor_set(v___x_145_, 2, v___x_144_);
lean_ctor_set(v___x_145_, 3, v_options_142_);
v___x_146_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v_msgData_136_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v_msgData_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
return v_res_152_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(uint8_t v___y_161_, uint8_t v_suppressElabErrors_162_, lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_163_) == 1)
{
lean_object* v_pre_164_; 
v_pre_164_ = lean_ctor_get(v_x_163_, 0);
switch(lean_obj_tag(v_pre_164_))
{
case 1:
{
lean_object* v_pre_165_; 
v_pre_165_ = lean_ctor_get(v_pre_164_, 0);
switch(lean_obj_tag(v_pre_165_))
{
case 0:
{
lean_object* v_str_166_; lean_object* v_str_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_str_166_ = lean_ctor_get(v_x_163_, 1);
v_str_167_ = lean_ctor_get(v_pre_164_, 1);
v___x_168_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0));
v___x_169_ = lean_string_dec_eq(v_str_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1));
v___x_171_ = lean_string_dec_eq(v_str_167_, v___x_170_);
if (v___x_171_ == 0)
{
return v___y_161_;
}
else
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2));
v___x_173_ = lean_string_dec_eq(v_str_166_, v___x_172_);
if (v___x_173_ == 0)
{
return v___y_161_;
}
else
{
return v_suppressElabErrors_162_;
}
}
}
else
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3));
v___x_175_ = lean_string_dec_eq(v_str_166_, v___x_174_);
if (v___x_175_ == 0)
{
return v___y_161_;
}
else
{
return v_suppressElabErrors_162_;
}
}
}
case 1:
{
lean_object* v_pre_176_; 
v_pre_176_ = lean_ctor_get(v_pre_165_, 0);
if (lean_obj_tag(v_pre_176_) == 0)
{
lean_object* v_str_177_; lean_object* v_str_178_; lean_object* v_str_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_str_177_ = lean_ctor_get(v_x_163_, 1);
v_str_178_ = lean_ctor_get(v_pre_164_, 1);
v_str_179_ = lean_ctor_get(v_pre_165_, 1);
v___x_180_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4));
v___x_181_ = lean_string_dec_eq(v_str_179_, v___x_180_);
if (v___x_181_ == 0)
{
return v___y_161_;
}
else
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5));
v___x_183_ = lean_string_dec_eq(v_str_178_, v___x_182_);
if (v___x_183_ == 0)
{
return v___y_161_;
}
else
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6));
v___x_185_ = lean_string_dec_eq(v_str_177_, v___x_184_);
if (v___x_185_ == 0)
{
return v___y_161_;
}
else
{
return v_suppressElabErrors_162_;
}
}
}
}
else
{
return v___y_161_;
}
}
default: 
{
return v___y_161_;
}
}
}
case 0:
{
lean_object* v_str_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_str_186_ = lean_ctor_get(v_x_163_, 1);
v___x_187_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7));
v___x_188_ = lean_string_dec_eq(v_str_186_, v___x_187_);
if (v___x_188_ == 0)
{
return v___y_161_;
}
else
{
return v_suppressElabErrors_162_;
}
}
default: 
{
return v___y_161_;
}
}
}
else
{
return v___y_161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed(lean_object* v___y_189_, lean_object* v_suppressElabErrors_190_, lean_object* v_x_191_){
_start:
{
uint8_t v___y_3122__boxed_192_; uint8_t v_suppressElabErrors_boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v___y_3122__boxed_192_ = lean_unbox(v___y_189_);
v_suppressElabErrors_boxed_193_ = lean_unbox(v_suppressElabErrors_190_);
v_res_194_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v___y_3122__boxed_192_, v_suppressElabErrors_boxed_193_, v_x_191_);
lean_dec(v_x_191_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(lean_object* v_opts_196_, lean_object* v_opt_197_){
_start:
{
lean_object* v_name_198_; lean_object* v_defValue_199_; lean_object* v_map_200_; lean_object* v___x_201_; 
v_name_198_ = lean_ctor_get(v_opt_197_, 0);
v_defValue_199_ = lean_ctor_get(v_opt_197_, 1);
v_map_200_ = lean_ctor_get(v_opts_196_, 0);
v___x_201_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_200_, v_name_198_);
if (lean_obj_tag(v___x_201_) == 0)
{
uint8_t v___x_202_; 
v___x_202_ = lean_unbox(v_defValue_199_);
return v___x_202_;
}
else
{
lean_object* v_val_203_; 
v_val_203_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_val_203_);
lean_dec_ref_known(v___x_201_, 1);
if (lean_obj_tag(v_val_203_) == 1)
{
uint8_t v_v_204_; 
v_v_204_ = lean_ctor_get_uint8(v_val_203_, 0);
lean_dec_ref_known(v_val_203_, 0);
return v_v_204_;
}
else
{
uint8_t v___x_205_; 
lean_dec(v_val_203_);
v___x_205_ = lean_unbox(v_defValue_199_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_206_, lean_object* v_opt_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_opts_206_, v_opt_207_);
lean_dec_ref(v_opt_207_);
lean_dec_ref(v_opts_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(lean_object* v_ref_211_, lean_object* v_msgData_212_, uint8_t v_severity_213_, uint8_t v_isSilent_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; uint8_t v___y_222_; uint8_t v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_255_; uint8_t v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; uint8_t v___y_259_; lean_object* v___y_260_; uint8_t v___y_261_; lean_object* v___y_262_; lean_object* v___y_280_; lean_object* v___y_281_; uint8_t v___y_282_; lean_object* v___y_283_; uint8_t v___y_284_; uint8_t v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_291_; uint8_t v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; uint8_t v___y_296_; uint8_t v___y_297_; uint8_t v___x_302_; uint8_t v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; uint8_t v___y_309_; uint8_t v___y_310_; uint8_t v___y_312_; uint8_t v___x_327_; 
v___x_302_ = 2;
v___x_327_ = l_Lean_instBEqMessageSeverity_beq(v_severity_213_, v___x_302_);
if (v___x_327_ == 0)
{
v___y_312_ = v___x_327_;
goto v___jp_311_;
}
else
{
uint8_t v___x_328_; 
lean_inc_ref(v_msgData_212_);
v___x_328_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_212_);
v___y_312_ = v___x_328_;
goto v___jp_311_;
}
v___jp_218_:
{
lean_object* v___x_228_; lean_object* v_currNamespace_229_; lean_object* v_openDecls_230_; lean_object* v_env_231_; lean_object* v_nextMacroScope_232_; lean_object* v_ngen_233_; lean_object* v_auxDeclNGen_234_; lean_object* v_traceState_235_; lean_object* v_cache_236_; lean_object* v_messages_237_; lean_object* v_infoState_238_; lean_object* v_snapshotTasks_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_253_; 
v___x_228_ = lean_st_ref_take(v___y_227_);
v_currNamespace_229_ = lean_ctor_get(v___y_226_, 6);
v_openDecls_230_ = lean_ctor_get(v___y_226_, 7);
v_env_231_ = lean_ctor_get(v___x_228_, 0);
v_nextMacroScope_232_ = lean_ctor_get(v___x_228_, 1);
v_ngen_233_ = lean_ctor_get(v___x_228_, 2);
v_auxDeclNGen_234_ = lean_ctor_get(v___x_228_, 3);
v_traceState_235_ = lean_ctor_get(v___x_228_, 4);
v_cache_236_ = lean_ctor_get(v___x_228_, 5);
v_messages_237_ = lean_ctor_get(v___x_228_, 6);
v_infoState_238_ = lean_ctor_get(v___x_228_, 7);
v_snapshotTasks_239_ = lean_ctor_get(v___x_228_, 8);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_253_ == 0)
{
v___x_241_ = v___x_228_;
v_isShared_242_ = v_isSharedCheck_253_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_snapshotTasks_239_);
lean_inc(v_infoState_238_);
lean_inc(v_messages_237_);
lean_inc(v_cache_236_);
lean_inc(v_traceState_235_);
lean_inc(v_auxDeclNGen_234_);
lean_inc(v_ngen_233_);
lean_inc(v_nextMacroScope_232_);
lean_inc(v_env_231_);
lean_dec(v___x_228_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_253_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
lean_inc(v_openDecls_230_);
lean_inc(v_currNamespace_229_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_currNamespace_229_);
lean_ctor_set(v___x_243_, 1, v_openDecls_230_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___y_220_);
lean_inc_ref(v___y_221_);
lean_inc_ref(v___y_224_);
v___x_245_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_245_, 0, v___y_224_);
lean_ctor_set(v___x_245_, 1, v___y_225_);
lean_ctor_set(v___x_245_, 2, v___y_219_);
lean_ctor_set(v___x_245_, 3, v___y_221_);
lean_ctor_set(v___x_245_, 4, v___x_244_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5, v___y_223_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5 + 1, v___y_222_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5 + 2, v_isSilent_214_);
v___x_246_ = l_Lean_MessageLog_add(v___x_245_, v_messages_237_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 6, v___x_246_);
v___x_248_ = v___x_241_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_env_231_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_nextMacroScope_232_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_ngen_233_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_auxDeclNGen_234_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_traceState_235_);
lean_ctor_set(v_reuseFailAlloc_252_, 5, v_cache_236_);
lean_ctor_set(v_reuseFailAlloc_252_, 6, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_252_, 7, v_infoState_238_);
lean_ctor_set(v_reuseFailAlloc_252_, 8, v_snapshotTasks_239_);
v___x_248_ = v_reuseFailAlloc_252_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_st_ref_set(v___y_227_, v___x_248_);
v___x_250_ = lean_box(0);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
}
v___jp_254_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_278_; 
v___x_263_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_212_);
v___x_264_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v___x_263_, v___y_215_, v___y_216_);
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_278_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_278_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_278_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_inc_ref_n(v___y_258_, 2);
v___x_269_ = l_Lean_FileMap_toPosition(v___y_258_, v___y_257_);
lean_dec(v___y_257_);
v___x_270_ = l_Lean_FileMap_toPosition(v___y_258_, v___y_262_);
lean_dec(v___y_262_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
v___x_272_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0));
if (v___y_256_ == 0)
{
lean_del_object(v___x_267_);
lean_dec_ref(v___y_255_);
v___y_219_ = v___x_271_;
v___y_220_ = v_a_265_;
v___y_221_ = v___x_272_;
v___y_222_ = v___y_259_;
v___y_223_ = v___y_261_;
v___y_224_ = v___y_260_;
v___y_225_ = v___x_269_;
v___y_226_ = v___y_215_;
v___y_227_ = v___y_216_;
goto v___jp_218_;
}
else
{
uint8_t v___x_273_; 
lean_inc(v_a_265_);
v___x_273_ = l_Lean_MessageData_hasTag(v___y_255_, v_a_265_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec_ref_known(v___x_271_, 1);
lean_dec_ref(v___x_269_);
lean_dec(v_a_265_);
v___x_274_ = lean_box(0);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_274_);
v___x_276_ = v___x_267_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
else
{
lean_del_object(v___x_267_);
v___y_219_ = v___x_271_;
v___y_220_ = v_a_265_;
v___y_221_ = v___x_272_;
v___y_222_ = v___y_259_;
v___y_223_ = v___y_261_;
v___y_224_ = v___y_260_;
v___y_225_ = v___x_269_;
v___y_226_ = v___y_215_;
v___y_227_ = v___y_216_;
goto v___jp_218_;
}
}
}
}
v___jp_279_:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Syntax_getTailPos_x3f(v___y_281_, v___y_285_);
lean_dec(v___y_281_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_inc(v___y_287_);
v___y_255_ = v___y_280_;
v___y_256_ = v___y_282_;
v___y_257_ = v___y_287_;
v___y_258_ = v___y_283_;
v___y_259_ = v___y_284_;
v___y_260_ = v___y_286_;
v___y_261_ = v___y_285_;
v___y_262_ = v___y_287_;
goto v___jp_254_;
}
else
{
lean_object* v_val_289_; 
v_val_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_val_289_);
lean_dec_ref_known(v___x_288_, 1);
v___y_255_ = v___y_280_;
v___y_256_ = v___y_282_;
v___y_257_ = v___y_287_;
v___y_258_ = v___y_283_;
v___y_259_ = v___y_284_;
v___y_260_ = v___y_286_;
v___y_261_ = v___y_285_;
v___y_262_ = v_val_289_;
goto v___jp_254_;
}
}
v___jp_290_:
{
lean_object* v_ref_298_; lean_object* v___x_299_; 
v_ref_298_ = l_Lean_replaceRef(v_ref_211_, v___y_294_);
v___x_299_ = l_Lean_Syntax_getPos_x3f(v_ref_298_, v___y_296_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_unsigned_to_nat(0u);
v___y_280_ = v___y_291_;
v___y_281_ = v_ref_298_;
v___y_282_ = v___y_292_;
v___y_283_ = v___y_293_;
v___y_284_ = v___y_297_;
v___y_285_ = v___y_296_;
v___y_286_ = v___y_295_;
v___y_287_ = v___x_300_;
goto v___jp_279_;
}
else
{
lean_object* v_val_301_; 
v_val_301_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v___x_299_, 1);
v___y_280_ = v___y_291_;
v___y_281_ = v_ref_298_;
v___y_282_ = v___y_292_;
v___y_283_ = v___y_293_;
v___y_284_ = v___y_297_;
v___y_285_ = v___y_296_;
v___y_286_ = v___y_295_;
v___y_287_ = v_val_301_;
goto v___jp_279_;
}
}
v___jp_303_:
{
if (v___y_310_ == 0)
{
v___y_291_ = v___y_305_;
v___y_292_ = v___y_304_;
v___y_293_ = v___y_306_;
v___y_294_ = v___y_307_;
v___y_295_ = v___y_308_;
v___y_296_ = v___y_309_;
v___y_297_ = v_severity_213_;
goto v___jp_290_;
}
else
{
v___y_291_ = v___y_305_;
v___y_292_ = v___y_304_;
v___y_293_ = v___y_306_;
v___y_294_ = v___y_307_;
v___y_295_ = v___y_308_;
v___y_296_ = v___y_309_;
v___y_297_ = v___x_302_;
goto v___jp_290_;
}
}
v___jp_311_:
{
if (v___y_312_ == 0)
{
lean_object* v_fileName_313_; lean_object* v_fileMap_314_; lean_object* v_options_315_; lean_object* v_ref_316_; uint8_t v_suppressElabErrors_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___f_320_; uint8_t v___x_321_; uint8_t v___x_322_; 
v_fileName_313_ = lean_ctor_get(v___y_215_, 0);
v_fileMap_314_ = lean_ctor_get(v___y_215_, 1);
v_options_315_ = lean_ctor_get(v___y_215_, 2);
v_ref_316_ = lean_ctor_get(v___y_215_, 5);
v_suppressElabErrors_317_ = lean_ctor_get_uint8(v___y_215_, sizeof(void*)*14 + 1);
v___x_318_ = lean_box(v___y_312_);
v___x_319_ = lean_box(v_suppressElabErrors_317_);
v___f_320_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_320_, 0, v___x_318_);
lean_closure_set(v___f_320_, 1, v___x_319_);
v___x_321_ = 1;
v___x_322_ = l_Lean_instBEqMessageSeverity_beq(v_severity_213_, v___x_321_);
if (v___x_322_ == 0)
{
v___y_304_ = v_suppressElabErrors_317_;
v___y_305_ = v___f_320_;
v___y_306_ = v_fileMap_314_;
v___y_307_ = v_ref_316_;
v___y_308_ = v_fileName_313_;
v___y_309_ = v___y_312_;
v___y_310_ = v___x_322_;
goto v___jp_303_;
}
else
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = l_Lean_warningAsError;
v___x_324_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_options_315_, v___x_323_);
v___y_304_ = v_suppressElabErrors_317_;
v___y_305_ = v___f_320_;
v___y_306_ = v_fileMap_314_;
v___y_307_ = v_ref_316_;
v___y_308_ = v_fileName_313_;
v___y_309_ = v___y_312_;
v___y_310_ = v___x_324_;
goto v___jp_303_;
}
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec_ref(v_msgData_212_);
v___x_325_ = lean_box(0);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___boxed(lean_object* v_ref_329_, lean_object* v_msgData_330_, lean_object* v_severity_331_, lean_object* v_isSilent_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
uint8_t v_severity_boxed_336_; uint8_t v_isSilent_boxed_337_; lean_object* v_res_338_; 
v_severity_boxed_336_ = lean_unbox(v_severity_331_);
v_isSilent_boxed_337_ = lean_unbox(v_isSilent_332_);
v_res_338_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_329_, v_msgData_330_, v_severity_boxed_336_, v_isSilent_boxed_337_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v_ref_329_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(lean_object* v_ref_339_, lean_object* v_msgData_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
uint8_t v___x_344_; uint8_t v___x_345_; lean_object* v___x_346_; 
v___x_344_ = 1;
v___x_345_ = 0;
v___x_346_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_339_, v_msgData_340_, v___x_344_, v___x_345_, v___y_341_, v___y_342_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(lean_object* v_ref_347_, lean_object* v_msgData_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_347_, v_msgData_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v_ref_347_);
return v_res_352_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__0));
v___x_355_ = l_Lean_stringToMessageData(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__2));
v___x_358_ = l_Lean_stringToMessageData(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__4));
v___x_361_ = l_Lean_stringToMessageData(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__6));
v___x_364_ = l_Lean_stringToMessageData(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__8));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__10));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__12));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone(lean_object* v_hints_374_, lean_object* v_reason_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_ref_379_; lean_object* v_terminationBy_x3f_x3f_380_; lean_object* v_terminationBy_x3f_381_; lean_object* v_partialFixpoint_x3f_382_; lean_object* v_decreasingBy_x3f_383_; lean_object* v___y_385_; lean_object* v___y_386_; 
v_ref_379_ = lean_ctor_get(v_hints_374_, 0);
lean_inc(v_ref_379_);
v_terminationBy_x3f_x3f_380_ = lean_ctor_get(v_hints_374_, 1);
lean_inc(v_terminationBy_x3f_x3f_380_);
v_terminationBy_x3f_381_ = lean_ctor_get(v_hints_374_, 2);
lean_inc(v_terminationBy_x3f_381_);
v_partialFixpoint_x3f_382_ = lean_ctor_get(v_hints_374_, 3);
lean_inc(v_partialFixpoint_x3f_382_);
v_decreasingBy_x3f_383_ = lean_ctor_get(v_hints_374_, 4);
lean_inc(v_decreasingBy_x3f_383_);
lean_dec_ref(v_hints_374_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_380_) == 0)
{
if (lean_obj_tag(v_terminationBy_x3f_381_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_383_) == 0)
{
lean_dec(v_ref_379_);
if (lean_obj_tag(v_partialFixpoint_x3f_382_) == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec_ref(v_reason_375_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
else
{
lean_object* v_val_393_; uint8_t v_fixpointType_394_; 
v_val_393_ = lean_ctor_get(v_partialFixpoint_x3f_382_, 0);
lean_inc(v_val_393_);
lean_dec_ref_known(v_partialFixpoint_x3f_382_, 1);
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
v___x_397_ = l_Lean_stringToMessageData(v_reason_375_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_395_, v___x_398_, v_a_376_, v_a_377_);
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
v___x_402_ = l_Lean_stringToMessageData(v_reason_375_);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_400_, v___x_403_, v_a_376_, v_a_377_);
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
v___x_407_ = l_Lean_stringToMessageData(v_reason_375_);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_405_, v___x_408_, v_a_376_, v_a_377_);
lean_dec(v_ref_405_);
return v___x_409_;
}
}
}
}
else
{
if (lean_obj_tag(v_partialFixpoint_x3f_382_) == 0)
{
lean_object* v_val_410_; lean_object* v_ref_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_ref_379_);
v_val_410_ = lean_ctor_get(v_decreasingBy_x3f_383_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v_decreasingBy_x3f_383_, 1);
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
v___x_416_ = l_Lean_stringToMessageData(v_reason_375_);
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
v___x_419_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_411_, v___x_418_, v_a_376_, v_a_377_);
lean_dec(v_ref_411_);
return v___x_419_;
}
}
}
else
{
lean_dec_ref_known(v_decreasingBy_x3f_383_, 1);
lean_dec(v_partialFixpoint_x3f_382_);
v___y_385_ = v_a_376_;
v___y_386_ = v_a_377_;
goto v___jp_384_;
}
}
}
else
{
if (lean_obj_tag(v_decreasingBy_x3f_383_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_382_) == 0)
{
lean_object* v_val_423_; lean_object* v_ref_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_ref_379_);
v_val_423_ = lean_ctor_get(v_terminationBy_x3f_381_, 0);
lean_inc(v_val_423_);
lean_dec_ref_known(v_terminationBy_x3f_381_, 1);
v_ref_424_ = lean_ctor_get(v_val_423_, 0);
lean_inc(v_ref_424_);
lean_dec(v_val_423_);
v___x_425_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__11, &l_Lean_Elab_TerminationHints_ensureNone___closed__11_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11);
v___x_426_ = l_Lean_stringToMessageData(v_reason_375_);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_424_, v___x_427_, v_a_376_, v_a_377_);
lean_dec(v_ref_424_);
return v___x_428_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_381_, 1);
lean_dec(v_partialFixpoint_x3f_382_);
v___y_385_ = v_a_376_;
v___y_386_ = v_a_377_;
goto v___jp_384_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_381_, 1);
lean_dec(v_decreasingBy_x3f_383_);
lean_dec(v_partialFixpoint_x3f_382_);
v___y_385_ = v_a_376_;
v___y_386_ = v_a_377_;
goto v___jp_384_;
}
}
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_381_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_383_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_382_) == 0)
{
lean_object* v_val_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec(v_ref_379_);
v_val_429_ = lean_ctor_get(v_terminationBy_x3f_x3f_380_, 0);
lean_inc(v_val_429_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_380_, 1);
v___x_430_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__13, &l_Lean_Elab_TerminationHints_ensureNone___closed__13_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13);
v___x_431_ = l_Lean_stringToMessageData(v_reason_375_);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_val_429_, v___x_432_, v_a_376_, v_a_377_);
lean_dec(v_val_429_);
return v___x_433_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_380_, 1);
lean_dec(v_partialFixpoint_x3f_382_);
v___y_385_ = v_a_376_;
v___y_386_ = v_a_377_;
goto v___jp_384_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_380_, 1);
lean_dec(v_decreasingBy_x3f_383_);
lean_dec(v_partialFixpoint_x3f_382_);
v___y_385_ = v_a_376_;
v___y_386_ = v_a_377_;
goto v___jp_384_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_380_, 1);
lean_dec(v_decreasingBy_x3f_383_);
lean_dec(v_partialFixpoint_x3f_382_);
lean_dec(v_terminationBy_x3f_381_);
v___y_385_ = v_a_376_;
v___y_386_ = v_a_377_;
goto v___jp_384_;
}
}
v___jp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__1, &l_Lean_Elab_TerminationHints_ensureNone___closed__1_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1);
v___x_388_ = l_Lean_stringToMessageData(v_reason_375_);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_379_, v___x_389_, v___y_385_, v___y_386_);
lean_dec(v_ref_379_);
return v___x_390_;
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
lean_object* v_ref_456_; lean_object* v_terminationBy_x3f_x3f_457_; lean_object* v_terminationBy_x3f_458_; lean_object* v_partialFixpoint_x3f_459_; lean_object* v_decreasingBy_x3f_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_469_; 
v_ref_456_ = lean_ctor_get(v_hints_454_, 0);
v_terminationBy_x3f_x3f_457_ = lean_ctor_get(v_hints_454_, 1);
v_terminationBy_x3f_458_ = lean_ctor_get(v_hints_454_, 2);
v_partialFixpoint_x3f_459_ = lean_ctor_get(v_hints_454_, 3);
v_decreasingBy_x3f_460_ = lean_ctor_get(v_hints_454_, 4);
v_isSharedCheck_469_ = !lean_is_exclusive(v_hints_454_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v_hints_454_, 5);
lean_dec(v_unused_470_);
v___x_462_ = v_hints_454_;
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_decreasingBy_x3f_460_);
lean_inc(v_partialFixpoint_x3f_459_);
lean_inc(v_terminationBy_x3f_458_);
lean_inc(v_terminationBy_x3f_x3f_457_);
lean_inc(v_ref_456_);
lean_dec(v_hints_454_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = l_Lean_Expr_getNumHeadLambdas(v_value_455_);
v___x_465_ = lean_nat_sub(v___x_464_, v_headerParams_453_);
lean_dec(v___x_464_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 5, v___x_465_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_ref_456_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_terminationBy_x3f_x3f_457_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_terminationBy_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_partialFixpoint_x3f_459_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_decreasingBy_x3f_460_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(lean_object* v_headerParams_471_, lean_object* v_hints_472_, lean_object* v_value_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v_headerParams_471_, v_hints_472_, v_value_473_);
lean_dec_ref(v_value_473_);
lean_dec(v_headerParams_471_);
return v_res_474_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3));
v___x_482_ = l_Lean_MessageData_ofFormat(v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(lean_object* v_a_483_){
_start:
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_dec_eq(v_a_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_486_ = l_Nat_reprFast(v_a_483_);
v___x_487_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
v___x_488_ = l_Lean_MessageData_ofFormat(v___x_487_);
v___x_489_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; 
lean_dec(v_a_483_);
v___x_491_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(lean_object* v_msgData_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; lean_object* v_env_499_; lean_object* v___x_500_; lean_object* v_mctx_501_; lean_object* v_lctx_502_; lean_object* v_options_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_498_ = lean_st_ref_get(v___y_496_);
v_env_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc_ref(v_env_499_);
lean_dec(v___x_498_);
v___x_500_ = lean_st_ref_get(v___y_494_);
v_mctx_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc_ref(v_mctx_501_);
lean_dec(v___x_500_);
v_lctx_502_ = lean_ctor_get(v___y_493_, 2);
v_options_503_ = lean_ctor_get(v___y_495_, 2);
lean_inc_ref(v_options_503_);
lean_inc_ref(v_lctx_502_);
v___x_504_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_504_, 0, v_env_499_);
lean_ctor_set(v___x_504_, 1, v_mctx_501_);
lean_ctor_set(v___x_504_, 2, v_lctx_502_);
lean_ctor_set(v___x_504_, 3, v_options_503_);
v___x_505_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_msgData_492_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(lean_object* v_msg_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_ref_520_; lean_object* v___x_521_; lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
v_ref_520_ = lean_ctor_get(v___y_517_, 5);
v___x_521_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msg_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_530_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
lean_inc(v_ref_520_);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v_ref_520_);
lean_ctor_set(v___x_526_, 1, v_a_522_);
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 1);
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_msg_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object* v_ref_538_, lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_fileName_545_; lean_object* v_fileMap_546_; lean_object* v_options_547_; lean_object* v_currRecDepth_548_; lean_object* v_maxRecDepth_549_; lean_object* v_ref_550_; lean_object* v_currNamespace_551_; lean_object* v_openDecls_552_; lean_object* v_initHeartbeats_553_; lean_object* v_maxHeartbeats_554_; lean_object* v_quotContext_555_; lean_object* v_currMacroScope_556_; uint8_t v_diag_557_; lean_object* v_cancelTk_x3f_558_; uint8_t v_suppressElabErrors_559_; lean_object* v_inheritedTraceOptions_560_; lean_object* v_ref_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_fileName_545_ = lean_ctor_get(v___y_542_, 0);
v_fileMap_546_ = lean_ctor_get(v___y_542_, 1);
v_options_547_ = lean_ctor_get(v___y_542_, 2);
v_currRecDepth_548_ = lean_ctor_get(v___y_542_, 3);
v_maxRecDepth_549_ = lean_ctor_get(v___y_542_, 4);
v_ref_550_ = lean_ctor_get(v___y_542_, 5);
v_currNamespace_551_ = lean_ctor_get(v___y_542_, 6);
v_openDecls_552_ = lean_ctor_get(v___y_542_, 7);
v_initHeartbeats_553_ = lean_ctor_get(v___y_542_, 8);
v_maxHeartbeats_554_ = lean_ctor_get(v___y_542_, 9);
v_quotContext_555_ = lean_ctor_get(v___y_542_, 10);
v_currMacroScope_556_ = lean_ctor_get(v___y_542_, 11);
v_diag_557_ = lean_ctor_get_uint8(v___y_542_, sizeof(void*)*14);
v_cancelTk_x3f_558_ = lean_ctor_get(v___y_542_, 12);
v_suppressElabErrors_559_ = lean_ctor_get_uint8(v___y_542_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_560_ = lean_ctor_get(v___y_542_, 13);
v_ref_561_ = l_Lean_replaceRef(v_ref_538_, v_ref_550_);
lean_inc_ref(v_inheritedTraceOptions_560_);
lean_inc(v_cancelTk_x3f_558_);
lean_inc(v_currMacroScope_556_);
lean_inc(v_quotContext_555_);
lean_inc(v_maxHeartbeats_554_);
lean_inc(v_initHeartbeats_553_);
lean_inc(v_openDecls_552_);
lean_inc(v_currNamespace_551_);
lean_inc(v_maxRecDepth_549_);
lean_inc(v_currRecDepth_548_);
lean_inc_ref(v_options_547_);
lean_inc_ref(v_fileMap_546_);
lean_inc_ref(v_fileName_545_);
v___x_562_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_562_, 0, v_fileName_545_);
lean_ctor_set(v___x_562_, 1, v_fileMap_546_);
lean_ctor_set(v___x_562_, 2, v_options_547_);
lean_ctor_set(v___x_562_, 3, v_currRecDepth_548_);
lean_ctor_set(v___x_562_, 4, v_maxRecDepth_549_);
lean_ctor_set(v___x_562_, 5, v_ref_561_);
lean_ctor_set(v___x_562_, 6, v_currNamespace_551_);
lean_ctor_set(v___x_562_, 7, v_openDecls_552_);
lean_ctor_set(v___x_562_, 8, v_initHeartbeats_553_);
lean_ctor_set(v___x_562_, 9, v_maxHeartbeats_554_);
lean_ctor_set(v___x_562_, 10, v_quotContext_555_);
lean_ctor_set(v___x_562_, 11, v_currMacroScope_556_);
lean_ctor_set(v___x_562_, 12, v_cancelTk_x3f_558_);
lean_ctor_set(v___x_562_, 13, v_inheritedTraceOptions_560_);
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*14, v_diag_557_);
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*14 + 1, v_suppressElabErrors_559_);
v___x_563_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_539_, v___y_540_, v___y_541_, v___x_562_, v___y_543_);
lean_dec_ref_known(v___x_562_, 14);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object* v_ref_564_, lean_object* v_msg_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_564_, v_msg_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v_ref_564_);
return v_res_571_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__0));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__3(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__2));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__5(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__4));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__9(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__8));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__12(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__11));
v___x_591_ = l_Lean_MessageData_ofFormat(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object* v_funName_592_, lean_object* v_extraParams_593_, lean_object* v_tb_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
uint8_t v_synthetic_600_; 
v_synthetic_600_ = lean_ctor_get_uint8(v_tb_594_, sizeof(void*)*3 + 1);
if (v_synthetic_600_ == 0)
{
lean_object* v_ref_601_; lean_object* v_vars_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_ref_601_ = lean_ctor_get(v_tb_594_, 0);
v_vars_602_ = lean_ctor_get(v_tb_594_, 1);
v___x_603_ = lean_array_get_size(v_vars_602_);
v___x_604_ = lean_nat_dec_lt(v_extraParams_593_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_extraParams_593_);
lean_dec(v_funName_592_);
v___x_605_ = lean_box(0);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_msg_617_; lean_object* v___x_618_; lean_object* v_ident_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_607_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_603_);
v___x_608_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__1, &l_Lean_Elab_TerminationBy_checkVars___closed__1_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__1);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
lean_inc(v_funName_592_);
v___x_610_ = l_Lean_MessageData_ofName(v_funName_592_);
v___x_611_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__3, &l_Lean_Elab_TerminationBy_checkVars___closed__3_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__3);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_593_);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__5, &l_Lean_Elab_TerminationBy_checkVars___closed__5_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__5);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v_msg_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_617_, 0, v___x_609_);
lean_ctor_set(v_msg_617_, 1, v___x_616_);
v___x_618_ = lean_unsigned_to_nat(0u);
v_ident_619_ = lean_array_fget_borrowed(v_vars_602_, v___x_618_);
v___x_620_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__7));
lean_inc(v_ident_619_);
v___x_621_ = l_Lean_Syntax_isOfKind(v_ident_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_dec(v_funName_592_);
v___x_622_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_601_, v_msg_617_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = l_Lean_TSyntax_getId(v_ident_619_);
v___x_624_ = l_Lean_Name_isSuffixOf(v___x_623_, v_funName_592_);
lean_dec(v_funName_592_);
lean_dec(v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_601_, v_msg_617_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
return v___x_625_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_msg_629_; lean_object* v___x_630_; 
v___x_626_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__9, &l_Lean_Elab_TerminationBy_checkVars___closed__9_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__9);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v_msg_617_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__12, &l_Lean_Elab_TerminationBy_checkVars___closed__12_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__12);
v_msg_629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_629_, 0, v___x_627_);
lean_ctor_set(v_msg_629_, 1, v___x_628_);
v___x_630_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_601_, v_msg_629_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
return v___x_630_;
}
}
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v_extraParams_593_);
lean_dec(v_funName_592_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object* v_funName_633_, lean_object* v_extraParams_634_, lean_object* v_tb_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Elab_TerminationBy_checkVars(v_funName_633_, v_extraParams_634_, v_tb_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec_ref(v_tb_635_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_object* v_00_u03b1_642_, lean_object* v_ref_643_, lean_object* v_msg_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_643_, v_msg_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object* v_00_u03b1_651_, lean_object* v_ref_652_, lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(v_00_u03b1_651_, v_ref_652_, v_msg_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v_ref_652_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_object* v_00_u03b1_660_, lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_668_, lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_668_, v_msg_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object* v_val_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_677_, 0, v_val_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object* v_stx_678_, lean_object* v_terminationBy_x3f_x3f_679_, lean_object* v_terminationBy_x3f_680_, lean_object* v_partialFixpoint_x3f_681_, lean_object* v___x_682_, lean_object* v_toPure_683_, lean_object* v_decreasingBy_x3f_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_685_, 0, v_stx_678_);
lean_ctor_set(v___x_685_, 1, v_terminationBy_x3f_x3f_679_);
lean_ctor_set(v___x_685_, 2, v_terminationBy_x3f_680_);
lean_ctor_set(v___x_685_, 3, v_partialFixpoint_x3f_681_);
lean_ctor_set(v___x_685_, 4, v_decreasingBy_x3f_684_);
lean_ctor_set(v___x_685_, 5, v___x_682_);
v___x_686_ = lean_apply_2(v_toPure_683_, lean_box(0), v___x_685_);
return v___x_686_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* v_stx_691_, lean_object* v_terminationBy_x3f_x3f_692_, lean_object* v_terminationBy_x3f_693_, lean_object* v___x_694_, lean_object* v_toPure_695_, lean_object* v_d_x3f_696_, lean_object* v_toBind_697_, lean_object* v_toFunctor_698_, lean_object* v___f_699_, lean_object* v___x_700_, lean_object* v___x_701_, lean_object* v___x_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v___x_705_, lean_object* v_partialFixpoint_x3f_706_){
_start:
{
lean_object* v___f_707_; 
lean_inc(v_toPure_695_);
v___f_707_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1), 7, 6);
lean_closure_set(v___f_707_, 0, v_stx_691_);
lean_closure_set(v___f_707_, 1, v_terminationBy_x3f_x3f_692_);
lean_closure_set(v___f_707_, 2, v_terminationBy_x3f_693_);
lean_closure_set(v___f_707_, 3, v_partialFixpoint_x3f_706_);
lean_closure_set(v___f_707_, 4, v___x_694_);
lean_closure_set(v___f_707_, 5, v_toPure_695_);
if (lean_obj_tag(v_d_x3f_696_) == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
lean_dec_ref(v___x_702_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_700_);
lean_dec_ref(v___f_699_);
lean_dec_ref(v_toFunctor_698_);
v___x_708_ = lean_box(0);
v___x_709_ = lean_apply_2(v_toPure_695_, lean_box(0), v___x_708_);
v___x_710_ = lean_apply_4(v_toBind_697_, lean_box(0), lean_box(0), v___x_709_, v___f_707_);
return v___x_710_;
}
else
{
lean_object* v_val_711_; lean_object* v_map_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_730_; 
v_val_711_ = lean_ctor_get(v_d_x3f_696_, 0);
lean_inc(v_val_711_);
lean_dec_ref_known(v_d_x3f_696_, 1);
v_map_712_ = lean_ctor_get(v_toFunctor_698_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v_toFunctor_698_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v_toFunctor_698_, 1);
lean_dec(v_unused_731_);
v___x_714_ = v_toFunctor_698_;
v_isShared_715_ = v_isSharedCheck_730_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_map_712_);
lean_dec(v_toFunctor_698_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_730_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___y_717_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_720_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0));
v___x_721_ = l_Lean_Name_mkStr4(v___x_700_, v___x_701_, v___x_702_, v___x_720_);
lean_inc(v_val_711_);
v___x_722_ = l_Lean_Syntax_isOfKind(v_val_711_, v___x_721_);
lean_dec(v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_del_object(v___x_714_);
lean_dec(v_toPure_695_);
v___x_723_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2, &l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2);
v___x_724_ = l_Lean_throwErrorAt___redArg(v_inst_703_, v_inst_704_, v_val_711_, v___x_723_);
v___y_717_ = v___x_724_;
goto v___jp_716_;
}
else
{
lean_object* v_tactic_725_; lean_object* v___x_727_; 
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
v_tactic_725_ = l_Lean_Syntax_getArg(v_val_711_, v___x_705_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v_tactic_725_);
lean_ctor_set(v___x_714_, 0, v_val_711_);
v___x_727_ = v___x_714_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_val_711_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_tactic_725_);
v___x_727_ = v_reuseFailAlloc_729_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; 
v___x_728_ = lean_apply_2(v_toPure_695_, lean_box(0), v___x_727_);
v___y_717_ = v___x_728_;
goto v___jp_716_;
}
}
v___jp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_apply_4(v_map_712_, lean_box(0), lean_box(0), v___f_699_, v___y_717_);
v___x_719_ = lean_apply_4(v_toBind_697_, lean_box(0), lean_box(0), v___x_718_, v___f_707_);
return v___x_719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object* v_stx_732_, lean_object* v_terminationBy_x3f_x3f_733_, lean_object* v_terminationBy_x3f_734_, lean_object* v___x_735_, lean_object* v_toPure_736_, lean_object* v_d_x3f_737_, lean_object* v_toBind_738_, lean_object* v_toFunctor_739_, lean_object* v___f_740_, lean_object* v___x_741_, lean_object* v___x_742_, lean_object* v___x_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v___x_746_, lean_object* v_partialFixpoint_x3f_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_732_, v_terminationBy_x3f_x3f_733_, v_terminationBy_x3f_734_, v___x_735_, v_toPure_736_, v_d_x3f_737_, v_toBind_738_, v_toFunctor_739_, v___f_740_, v___x_741_, v___x_742_, v___x_743_, v_inst_744_, v_inst_745_, v___x_746_, v_partialFixpoint_x3f_747_);
lean_dec(v___x_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object* v___f_749_, lean_object* v_partialFixpoint_x3f_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_apply_1(v___f_749_, v_partialFixpoint_x3f_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object* v_stx_755_, lean_object* v_terminationBy_x3f_x3f_756_, lean_object* v___x_757_, lean_object* v_toPure_758_, lean_object* v_d_x3f_759_, lean_object* v_toBind_760_, lean_object* v_toFunctor_761_, lean_object* v___f_762_, lean_object* v___x_763_, lean_object* v___x_764_, lean_object* v___x_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v___x_768_, lean_object* v_t_x3f_769_, lean_object* v_terminationBy_x3f_770_){
_start:
{
lean_object* v___f_771_; 
lean_inc(v___x_768_);
lean_inc_ref(v___x_765_);
lean_inc_ref(v___x_764_);
lean_inc_ref(v___x_763_);
lean_inc(v_toBind_760_);
lean_inc(v_toPure_758_);
v___f_771_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed), 16, 15);
lean_closure_set(v___f_771_, 0, v_stx_755_);
lean_closure_set(v___f_771_, 1, v_terminationBy_x3f_x3f_756_);
lean_closure_set(v___f_771_, 2, v_terminationBy_x3f_770_);
lean_closure_set(v___f_771_, 3, v___x_757_);
lean_closure_set(v___f_771_, 4, v_toPure_758_);
lean_closure_set(v___f_771_, 5, v_d_x3f_759_);
lean_closure_set(v___f_771_, 6, v_toBind_760_);
lean_closure_set(v___f_771_, 7, v_toFunctor_761_);
lean_closure_set(v___f_771_, 8, v___f_762_);
lean_closure_set(v___f_771_, 9, v___x_763_);
lean_closure_set(v___f_771_, 10, v___x_764_);
lean_closure_set(v___f_771_, 11, v___x_765_);
lean_closure_set(v___f_771_, 12, v_inst_766_);
lean_closure_set(v___f_771_, 13, v_inst_767_);
lean_closure_set(v___f_771_, 14, v___x_768_);
if (lean_obj_tag(v_t_x3f_769_) == 1)
{
lean_object* v_val_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_849_; 
v_val_772_ = lean_ctor_get(v_t_x3f_769_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v_t_x3f_769_);
if (v_isSharedCheck_849_ == 0)
{
v___x_774_ = v_t_x3f_769_;
v_isShared_775_ = v_isSharedCheck_849_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_val_772_);
lean_dec(v_t_x3f_769_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_849_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_776_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_765_);
lean_inc_ref(v___x_764_);
lean_inc_ref(v___x_763_);
v___x_777_ = l_Lean_Name_mkStr4(v___x_763_, v___x_764_, v___x_765_, v___x_776_);
lean_inc(v_val_772_);
v___x_778_ = l_Lean_Syntax_isOfKind(v_val_772_, v___x_777_);
lean_dec(v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_779_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_765_);
lean_inc_ref(v___x_764_);
lean_inc_ref(v___x_763_);
v___x_780_ = l_Lean_Name_mkStr4(v___x_763_, v___x_764_, v___x_765_, v___x_779_);
lean_inc(v_val_772_);
v___x_781_ = l_Lean_Syntax_isOfKind(v_val_772_, v___x_780_);
lean_dec(v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_782_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_783_ = l_Lean_Name_mkStr4(v___x_763_, v___x_764_, v___x_765_, v___x_782_);
lean_inc(v_val_772_);
v___x_784_ = l_Lean_Syntax_isOfKind(v_val_772_, v___x_783_);
lean_dec(v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_del_object(v___x_774_);
lean_dec(v_val_772_);
lean_dec(v___x_768_);
v___f_785_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_785_, 0, v___f_771_);
v___x_786_ = lean_box(0);
v___x_787_ = lean_apply_2(v_toPure_758_, lean_box(0), v___x_786_);
v___x_788_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_787_, v___f_785_);
return v___x_788_;
}
else
{
lean_object* v___f_789_; lean_object* v_term_x3f_791_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___f_789_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_789_, 0, v___f_771_);
v___x_799_ = l_Lean_Syntax_getArg(v_val_772_, v___x_768_);
v___x_800_ = l_Lean_Syntax_isNone(v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_801_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_799_);
v___x_802_ = l_Lean_Syntax_matchesNull(v___x_799_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec(v___x_799_);
lean_del_object(v___x_774_);
lean_dec(v_val_772_);
lean_dec(v___x_768_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_apply_2(v_toPure_758_, lean_box(0), v___x_803_);
v___x_805_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_804_, v___f_789_);
return v___x_805_;
}
else
{
lean_object* v_term_x3f_806_; lean_object* v___x_807_; 
v_term_x3f_806_ = l_Lean_Syntax_getArg(v___x_799_, v___x_768_);
lean_dec(v___x_768_);
lean_dec(v___x_799_);
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v_term_x3f_806_);
v_term_x3f_791_ = v___x_807_;
goto v___jp_790_;
}
}
else
{
lean_object* v___x_808_; 
lean_dec(v___x_799_);
lean_dec(v___x_768_);
v___x_808_ = lean_box(0);
v_term_x3f_791_ = v___x_808_;
goto v___jp_790_;
}
v___jp_790_:
{
uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_792_ = 2;
v___x_793_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_793_, 0, v_val_772_);
lean_ctor_set(v___x_793_, 1, v_term_x3f_791_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2, v___x_792_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_793_);
v___x_795_ = v___x_774_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_798_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_apply_2(v_toPure_758_, lean_box(0), v___x_795_);
v___x_797_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_796_, v___f_789_);
return v___x_797_;
}
}
}
}
else
{
lean_object* v___f_809_; lean_object* v_term_x3f_811_; lean_object* v___x_819_; uint8_t v___x_820_; 
lean_dec_ref(v___x_765_);
lean_dec_ref(v___x_764_);
lean_dec_ref(v___x_763_);
v___f_809_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_809_, 0, v___f_771_);
v___x_819_ = l_Lean_Syntax_getArg(v_val_772_, v___x_768_);
v___x_820_ = l_Lean_Syntax_isNone(v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_819_);
v___x_822_ = l_Lean_Syntax_matchesNull(v___x_819_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec(v___x_819_);
lean_del_object(v___x_774_);
lean_dec(v_val_772_);
lean_dec(v___x_768_);
v___x_823_ = lean_box(0);
v___x_824_ = lean_apply_2(v_toPure_758_, lean_box(0), v___x_823_);
v___x_825_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_824_, v___f_809_);
return v___x_825_;
}
else
{
lean_object* v_term_x3f_826_; lean_object* v___x_827_; 
v_term_x3f_826_ = l_Lean_Syntax_getArg(v___x_819_, v___x_768_);
lean_dec(v___x_768_);
lean_dec(v___x_819_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v_term_x3f_826_);
v_term_x3f_811_ = v___x_827_;
goto v___jp_810_;
}
}
else
{
lean_object* v___x_828_; 
lean_dec(v___x_819_);
lean_dec(v___x_768_);
v___x_828_ = lean_box(0);
v_term_x3f_811_ = v___x_828_;
goto v___jp_810_;
}
v___jp_810_:
{
uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_812_ = 1;
v___x_813_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_813_, 0, v_val_772_);
lean_ctor_set(v___x_813_, 1, v_term_x3f_811_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*2, v___x_812_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_813_);
v___x_815_ = v___x_774_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_818_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_apply_2(v_toPure_758_, lean_box(0), v___x_815_);
v___x_817_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_816_, v___f_809_);
return v___x_817_;
}
}
}
}
else
{
lean_object* v___f_829_; lean_object* v_term_x3f_831_; lean_object* v___x_839_; uint8_t v___x_840_; 
lean_dec_ref(v___x_765_);
lean_dec_ref(v___x_764_);
lean_dec_ref(v___x_763_);
v___f_829_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_829_, 0, v___f_771_);
v___x_839_ = l_Lean_Syntax_getArg(v_val_772_, v___x_768_);
v___x_840_ = l_Lean_Syntax_isNone(v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_839_);
v___x_842_ = l_Lean_Syntax_matchesNull(v___x_839_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec(v___x_839_);
lean_del_object(v___x_774_);
lean_dec(v_val_772_);
lean_dec(v___x_768_);
v___x_843_ = lean_box(0);
v___x_844_ = lean_apply_2(v_toPure_758_, lean_box(0), v___x_843_);
v___x_845_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_844_, v___f_829_);
return v___x_845_;
}
else
{
lean_object* v_term_x3f_846_; lean_object* v___x_847_; 
v_term_x3f_846_ = l_Lean_Syntax_getArg(v___x_839_, v___x_768_);
lean_dec(v___x_768_);
lean_dec(v___x_839_);
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v_term_x3f_846_);
v_term_x3f_831_ = v___x_847_;
goto v___jp_830_;
}
}
else
{
lean_object* v___x_848_; 
lean_dec(v___x_839_);
lean_dec(v___x_768_);
v___x_848_ = lean_box(0);
v_term_x3f_831_ = v___x_848_;
goto v___jp_830_;
}
v___jp_830_:
{
uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_832_ = 0;
v___x_833_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_833_, 0, v_val_772_);
lean_ctor_set(v___x_833_, 1, v_term_x3f_831_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*2, v___x_832_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_833_);
v___x_835_ = v___x_774_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_838_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_apply_2(v_toPure_758_, lean_box(0), v___x_835_);
v___x_837_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_836_, v___f_829_);
return v___x_837_;
}
}
}
}
}
else
{
lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v_t_x3f_769_);
lean_dec(v___x_768_);
lean_dec_ref(v___x_765_);
lean_dec_ref(v___x_764_);
lean_dec_ref(v___x_763_);
v___f_850_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_850_, 0, v___f_771_);
v___x_851_ = lean_box(0);
v___x_852_ = lean_apply_2(v_toPure_758_, lean_box(0), v___x_851_);
v___x_853_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_852_, v___f_850_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* v___f_854_, lean_object* v_terminationBy_x3f_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lean_apply_1(v___f_854_, v_terminationBy_x3f_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* v_stx_865_, lean_object* v___x_866_, lean_object* v_toPure_867_, lean_object* v_d_x3f_868_, lean_object* v_toBind_869_, lean_object* v_toFunctor_870_, lean_object* v___f_871_, lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v___x_874_, lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v___x_877_, lean_object* v_t_x3f_878_, lean_object* v_terminationBy_x3f_x3f_879_){
_start:
{
lean_object* v___f_880_; 
lean_inc(v_t_x3f_878_);
lean_inc(v___x_877_);
lean_inc_ref(v_inst_876_);
lean_inc_ref(v_inst_875_);
lean_inc_ref(v___x_874_);
lean_inc_ref(v___x_873_);
lean_inc_ref(v___x_872_);
lean_inc(v_toBind_869_);
lean_inc(v_toPure_867_);
lean_inc(v___x_866_);
v___f_880_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11), 16, 15);
lean_closure_set(v___f_880_, 0, v_stx_865_);
lean_closure_set(v___f_880_, 1, v_terminationBy_x3f_x3f_879_);
lean_closure_set(v___f_880_, 2, v___x_866_);
lean_closure_set(v___f_880_, 3, v_toPure_867_);
lean_closure_set(v___f_880_, 4, v_d_x3f_868_);
lean_closure_set(v___f_880_, 5, v_toBind_869_);
lean_closure_set(v___f_880_, 6, v_toFunctor_870_);
lean_closure_set(v___f_880_, 7, v___f_871_);
lean_closure_set(v___f_880_, 8, v___x_872_);
lean_closure_set(v___f_880_, 9, v___x_873_);
lean_closure_set(v___f_880_, 10, v___x_874_);
lean_closure_set(v___f_880_, 11, v_inst_875_);
lean_closure_set(v___f_880_, 12, v_inst_876_);
lean_closure_set(v___f_880_, 13, v___x_877_);
lean_closure_set(v___f_880_, 14, v_t_x3f_878_);
if (lean_obj_tag(v_t_x3f_878_) == 1)
{
lean_object* v_val_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_993_; 
v_val_881_ = lean_ctor_get(v_t_x3f_878_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v_t_x3f_878_);
if (v_isSharedCheck_993_ == 0)
{
v___x_883_ = v_t_x3f_878_;
v_isShared_884_ = v_isSharedCheck_993_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_val_881_);
lean_dec(v_t_x3f_878_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_993_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0));
lean_inc_ref(v___x_874_);
lean_inc_ref(v___x_873_);
lean_inc_ref(v___x_872_);
v___x_886_ = l_Lean_Name_mkStr4(v___x_872_, v___x_873_, v___x_874_, v___x_885_);
lean_inc(v_val_881_);
v___x_887_ = l_Lean_Syntax_isOfKind(v_val_881_, v___x_886_);
lean_dec(v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
lean_del_object(v___x_883_);
lean_dec(v___x_866_);
v___x_888_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1));
lean_inc_ref(v___x_874_);
lean_inc_ref(v___x_873_);
lean_inc_ref(v___x_872_);
v___x_889_ = l_Lean_Name_mkStr4(v___x_872_, v___x_873_, v___x_874_, v___x_888_);
lean_inc(v_val_881_);
v___x_890_ = l_Lean_Syntax_isOfKind(v_val_881_, v___x_889_);
lean_dec(v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_891_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_874_);
lean_inc_ref(v___x_873_);
lean_inc_ref(v___x_872_);
v___x_892_ = l_Lean_Name_mkStr4(v___x_872_, v___x_873_, v___x_874_, v___x_891_);
lean_inc(v_val_881_);
v___x_893_ = l_Lean_Syntax_isOfKind(v_val_881_, v___x_892_);
lean_dec(v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_894_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_874_);
lean_inc_ref(v___x_873_);
lean_inc_ref(v___x_872_);
v___x_895_ = l_Lean_Name_mkStr4(v___x_872_, v___x_873_, v___x_874_, v___x_894_);
lean_inc(v_val_881_);
v___x_896_ = l_Lean_Syntax_isOfKind(v_val_881_, v___x_895_);
lean_dec(v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_897_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_898_ = l_Lean_Name_mkStr4(v___x_872_, v___x_873_, v___x_874_, v___x_897_);
lean_inc(v_val_881_);
v___x_899_ = l_Lean_Syntax_isOfKind(v_val_881_, v___x_898_);
lean_dec(v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec(v___x_877_);
lean_dec(v_toPure_867_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_900_, 0, v___f_880_);
v___x_901_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_902_ = l_Lean_throwErrorAt___redArg(v_inst_875_, v_inst_876_, v_val_881_, v___x_901_);
v___x_903_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_902_, v___f_900_);
return v___x_903_;
}
else
{
lean_object* v___f_904_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___f_904_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_904_, 0, v___f_880_);
v___x_909_ = l_Lean_Syntax_getArg(v_val_881_, v___x_877_);
lean_dec(v___x_877_);
v___x_910_ = l_Lean_Syntax_isNone(v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(2u);
v___x_912_ = l_Lean_Syntax_matchesNull(v___x_909_, v___x_911_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec(v_toPure_867_);
v___x_913_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_914_ = l_Lean_throwErrorAt___redArg(v_inst_875_, v_inst_876_, v_val_881_, v___x_913_);
v___x_915_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_914_, v___f_904_);
return v___x_915_;
}
else
{
lean_dec(v_val_881_);
lean_dec_ref(v_inst_876_);
lean_dec_ref(v_inst_875_);
goto v___jp_905_;
}
}
else
{
lean_dec(v___x_909_);
lean_dec(v_val_881_);
lean_dec_ref(v_inst_876_);
lean_dec_ref(v_inst_875_);
goto v___jp_905_;
}
v___jp_905_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_box(0);
v___x_907_ = lean_apply_2(v_toPure_867_, lean_box(0), v___x_906_);
v___x_908_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_907_, v___f_904_);
return v___x_908_;
}
}
}
else
{
lean_object* v___f_916_; lean_object* v___x_921_; uint8_t v___x_922_; 
lean_dec_ref(v___x_874_);
lean_dec_ref(v___x_873_);
lean_dec_ref(v___x_872_);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_916_, 0, v___f_880_);
v___x_921_ = l_Lean_Syntax_getArg(v_val_881_, v___x_877_);
lean_dec(v___x_877_);
v___x_922_ = l_Lean_Syntax_isNone(v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_unsigned_to_nat(2u);
v___x_924_ = l_Lean_Syntax_matchesNull(v___x_921_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_toPure_867_);
v___x_925_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_926_ = l_Lean_throwErrorAt___redArg(v_inst_875_, v_inst_876_, v_val_881_, v___x_925_);
v___x_927_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_926_, v___f_916_);
return v___x_927_;
}
else
{
lean_dec(v_val_881_);
lean_dec_ref(v_inst_876_);
lean_dec_ref(v_inst_875_);
goto v___jp_917_;
}
}
else
{
lean_dec(v___x_921_);
lean_dec(v_val_881_);
lean_dec_ref(v_inst_876_);
lean_dec_ref(v_inst_875_);
goto v___jp_917_;
}
v___jp_917_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = lean_box(0);
v___x_919_ = lean_apply_2(v_toPure_867_, lean_box(0), v___x_918_);
v___x_920_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_919_, v___f_916_);
return v___x_920_;
}
}
}
else
{
lean_object* v___f_928_; lean_object* v___x_933_; uint8_t v___x_934_; 
lean_dec_ref(v___x_874_);
lean_dec_ref(v___x_873_);
lean_dec_ref(v___x_872_);
v___f_928_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_928_, 0, v___f_880_);
v___x_933_ = l_Lean_Syntax_getArg(v_val_881_, v___x_877_);
lean_dec(v___x_877_);
v___x_934_ = l_Lean_Syntax_isNone(v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = lean_unsigned_to_nat(2u);
v___x_936_ = l_Lean_Syntax_matchesNull(v___x_933_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec(v_toPure_867_);
v___x_937_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_938_ = l_Lean_throwErrorAt___redArg(v_inst_875_, v_inst_876_, v_val_881_, v___x_937_);
v___x_939_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_938_, v___f_928_);
return v___x_939_;
}
else
{
lean_dec(v_val_881_);
lean_dec_ref(v_inst_876_);
lean_dec_ref(v_inst_875_);
goto v___jp_929_;
}
}
else
{
lean_dec(v___x_933_);
lean_dec(v_val_881_);
lean_dec_ref(v_inst_876_);
lean_dec_ref(v_inst_875_);
goto v___jp_929_;
}
v___jp_929_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_box(0);
v___x_931_ = lean_apply_2(v_toPure_867_, lean_box(0), v___x_930_);
v___x_932_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_931_, v___f_928_);
return v___x_932_;
}
}
}
else
{
lean_object* v___f_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_val_881_);
lean_dec(v___x_877_);
lean_dec_ref(v_inst_876_);
lean_dec_ref(v_inst_875_);
lean_dec_ref(v___x_874_);
lean_dec_ref(v___x_873_);
lean_dec_ref(v___x_872_);
v___f_940_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_940_, 0, v___f_880_);
v___x_941_ = lean_box(0);
v___x_942_ = lean_apply_2(v_toPure_867_, lean_box(0), v___x_941_);
v___x_943_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_942_, v___f_940_);
return v___x_943_;
}
}
else
{
lean_object* v___f_944_; lean_object* v___y_946_; uint8_t v___y_947_; lean_object* v___y_948_; uint8_t v___y_949_; lean_object* v___y_957_; uint8_t v___y_958_; uint8_t v___y_959_; lean_object* v_s_966_; lean_object* v___x_984_; uint8_t v___x_985_; 
lean_dec_ref(v___x_874_);
lean_dec_ref(v___x_873_);
lean_dec_ref(v___x_872_);
v___f_944_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_944_, 0, v___f_880_);
v___x_984_ = l_Lean_Syntax_getArg(v_val_881_, v___x_877_);
v___x_985_ = l_Lean_Syntax_isNone(v___x_984_);
if (v___x_985_ == 0)
{
uint8_t v___x_986_; 
lean_inc(v___x_984_);
v___x_986_ = l_Lean_Syntax_matchesNull(v___x_984_, v___x_877_);
lean_dec(v___x_877_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v___x_984_);
lean_del_object(v___x_883_);
lean_dec(v_toPure_867_);
lean_dec(v___x_866_);
v___x_987_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_988_ = l_Lean_throwErrorAt___redArg(v_inst_875_, v_inst_876_, v_val_881_, v___x_987_);
v___x_989_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_988_, v___f_944_);
return v___x_989_;
}
else
{
lean_object* v_s_990_; lean_object* v___x_991_; 
v_s_990_ = l_Lean_Syntax_getArg(v___x_984_, v___x_866_);
lean_dec(v___x_984_);
v___x_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_991_, 0, v_s_990_);
v_s_966_ = v___x_991_;
goto v___jp_965_;
}
}
else
{
lean_object* v___x_992_; 
lean_dec(v___x_984_);
lean_dec(v___x_877_);
v___x_992_ = lean_box(0);
v_s_966_ = v___x_992_;
goto v___jp_965_;
}
v___jp_945_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_950_, 0, v_val_881_);
lean_ctor_set(v___x_950_, 1, v___y_948_);
lean_ctor_set(v___x_950_, 2, v___y_946_);
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*3, v___y_949_);
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*3 + 1, v___y_947_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_950_);
v___x_952_ = v___x_883_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_955_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_apply_2(v_toPure_867_, lean_box(0), v___x_952_);
v___x_954_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_953_, v___f_944_);
return v___x_954_;
}
}
v___jp_956_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_960_ = lean_mk_empty_array_with_capacity(v___x_866_);
lean_dec(v___x_866_);
v___x_961_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_961_, 0, v_val_881_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
lean_ctor_set(v___x_961_, 2, v___y_957_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*3, v___y_959_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*3 + 1, v___y_958_);
v___x_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
v___x_963_ = lean_apply_2(v_toPure_867_, lean_box(0), v___x_962_);
v___x_964_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_963_, v___f_944_);
return v___x_964_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_967_ = lean_unsigned_to_nat(2u);
v___x_968_ = l_Lean_Syntax_getArg(v_val_881_, v___x_967_);
lean_inc(v___x_968_);
v___x_969_ = l_Lean_Syntax_matchesNull(v___x_968_, v___x_967_);
if (v___x_969_ == 0)
{
uint8_t v___x_970_; 
lean_del_object(v___x_883_);
v___x_970_ = l_Lean_Syntax_matchesNull(v___x_968_, v___x_866_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec(v_s_966_);
lean_dec(v_toPure_867_);
lean_dec(v___x_866_);
v___x_971_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_972_ = l_Lean_throwErrorAt___redArg(v_inst_875_, v_inst_876_, v_val_881_, v___x_971_);
v___x_973_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_972_, v___f_944_);
return v___x_973_;
}
else
{
lean_object* v___x_974_; lean_object* v_body_975_; 
lean_dec_ref(v_inst_876_);
lean_dec_ref(v_inst_875_);
v___x_974_ = lean_unsigned_to_nat(3u);
v_body_975_ = l_Lean_Syntax_getArg(v_val_881_, v___x_974_);
if (lean_obj_tag(v_s_966_) == 0)
{
v___y_957_ = v_body_975_;
v___y_958_ = v___x_969_;
v___y_959_ = v___x_969_;
goto v___jp_956_;
}
else
{
lean_dec_ref_known(v_s_966_, 1);
v___y_957_ = v_body_975_;
v___y_958_ = v___x_969_;
v___y_959_ = v___x_970_;
goto v___jp_956_;
}
}
}
else
{
lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_976_ = l_Lean_Syntax_getArg(v___x_968_, v___x_866_);
lean_dec(v___x_968_);
lean_inc(v___x_976_);
v___x_977_ = l_Lean_Syntax_matchesNull(v___x_976_, v___x_866_);
lean_dec(v___x_866_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v_body_979_; lean_object* v_vars_980_; 
lean_dec_ref(v_inst_876_);
lean_dec_ref(v_inst_875_);
v___x_978_ = lean_unsigned_to_nat(3u);
v_body_979_ = l_Lean_Syntax_getArg(v_val_881_, v___x_978_);
v_vars_980_ = l_Lean_Syntax_getArgs(v___x_976_);
lean_dec(v___x_976_);
if (lean_obj_tag(v_s_966_) == 0)
{
v___y_946_ = v_body_979_;
v___y_947_ = v___x_977_;
v___y_948_ = v_vars_980_;
v___y_949_ = v___x_977_;
goto v___jp_945_;
}
else
{
lean_dec_ref_known(v_s_966_, 1);
v___y_946_ = v_body_979_;
v___y_947_ = v___x_977_;
v___y_948_ = v_vars_980_;
v___y_949_ = v___x_969_;
goto v___jp_945_;
}
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec(v___x_976_);
lean_dec(v_s_966_);
lean_del_object(v___x_883_);
lean_dec(v_toPure_867_);
v___x_981_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
v___x_982_ = l_Lean_throwErrorAt___redArg(v_inst_875_, v_inst_876_, v_val_881_, v___x_981_);
v___x_983_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_982_, v___f_944_);
return v___x_983_;
}
}
}
}
}
}
else
{
lean_object* v___f_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec(v_t_x3f_878_);
lean_dec(v___x_877_);
lean_dec_ref(v_inst_876_);
lean_dec_ref(v_inst_875_);
lean_dec_ref(v___x_874_);
lean_dec_ref(v___x_873_);
lean_dec_ref(v___x_872_);
lean_dec(v___x_866_);
v___f_994_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_994_, 0, v___f_880_);
v___x_995_ = lean_box(0);
v___x_996_ = lean_apply_2(v_toPure_867_, lean_box(0), v___x_995_);
v___x_997_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_996_, v___f_994_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* v___f_998_, lean_object* v_terminationBy_x3f_x3f_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_apply_1(v___f_998_, v_terminationBy_x3f_x3f_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_stx_1025_){
_start:
{
if (lean_obj_tag(v_stx_1025_) == 0)
{
lean_object* v_toApplicative_1026_; lean_object* v_toPure_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_toApplicative_1026_ = lean_ctor_get(v_inst_1023_, 0);
lean_inc_ref(v_toApplicative_1026_);
lean_dec_ref(v_inst_1024_);
lean_dec_ref(v_inst_1023_);
v_toPure_1027_ = lean_ctor_get(v_toApplicative_1026_, 1);
lean_inc(v_toPure_1027_);
lean_dec_ref(v_toApplicative_1026_);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1030_, 0, v_stx_1025_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
lean_ctor_set(v___x_1030_, 2, v___x_1029_);
lean_ctor_set(v___x_1030_, 3, v___x_1029_);
lean_ctor_set(v___x_1030_, 4, v___x_1029_);
lean_ctor_set(v___x_1030_, 5, v___x_1028_);
v___x_1031_ = lean_apply_2(v_toPure_1027_, lean_box(0), v___x_1030_);
return v___x_1031_;
}
else
{
lean_object* v_toApplicative_1032_; lean_object* v_toBind_1033_; lean_object* v_toFunctor_1034_; lean_object* v_toPure_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_toApplicative_1032_ = lean_ctor_get(v_inst_1023_, 0);
v_toBind_1033_ = lean_ctor_get(v_inst_1023_, 1);
v_toFunctor_1034_ = lean_ctor_get(v_toApplicative_1032_, 0);
v_toPure_1035_ = lean_ctor_get(v_toApplicative_1032_, 1);
v___x_1036_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__0));
v___x_1037_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__1));
v___x_1038_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__2));
v___x_1039_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__4));
lean_inc(v_stx_1025_);
v___x_1040_ = l_Lean_Syntax_isOfKind(v_stx_1025_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1041_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1042_ = lean_box(0);
lean_inc_n(v_stx_1025_, 2);
v___x_1043_ = l_Lean_Syntax_formatStx(v_stx_1025_, v___x_1042_, v___x_1040_);
v___x_1044_ = l_Std_Format_defWidth;
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = l_Std_Format_pretty(v___x_1043_, v___x_1044_, v___x_1045_, v___x_1045_);
v___x_1047_ = lean_string_append(v___x_1041_, v___x_1046_);
lean_dec_ref(v___x_1046_);
v___x_1048_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1049_ = lean_string_append(v___x_1047_, v___x_1048_);
v___x_1050_ = l_Lean_Syntax_getKind(v_stx_1025_);
v___x_1051_ = 1;
v___x_1052_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1050_, v___x_1051_);
v___x_1053_ = lean_string_append(v___x_1049_, v___x_1052_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
v___x_1055_ = l_Lean_MessageData_ofFormat(v___x_1054_);
v___x_1056_ = l_Lean_throwErrorAt___redArg(v_inst_1023_, v_inst_1024_, v_stx_1025_, v___x_1055_);
return v___x_1056_;
}
else
{
lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v_d_x3f_1062_; lean_object* v_t_x3f_1086_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___f_1057_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__7));
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1124_ = l_Lean_Syntax_getArg(v_stx_1025_, v___x_1058_);
v___x_1125_ = l_Lean_Syntax_isNone(v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1124_);
v___x_1127_ = l_Lean_Syntax_matchesNull(v___x_1124_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec(v___x_1124_);
v___x_1128_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1129_ = lean_box(0);
lean_inc_n(v_stx_1025_, 2);
v___x_1130_ = l_Lean_Syntax_formatStx(v_stx_1025_, v___x_1129_, v___x_1127_);
v___x_1131_ = l_Std_Format_defWidth;
v___x_1132_ = l_Std_Format_pretty(v___x_1130_, v___x_1131_, v___x_1058_, v___x_1058_);
v___x_1133_ = lean_string_append(v___x_1128_, v___x_1132_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1135_ = lean_string_append(v___x_1133_, v___x_1134_);
v___x_1136_ = l_Lean_Syntax_getKind(v_stx_1025_);
v___x_1137_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1136_, v___x_1040_);
v___x_1138_ = lean_string_append(v___x_1135_, v___x_1137_);
lean_dec_ref(v___x_1137_);
v___x_1139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
v___x_1140_ = l_Lean_MessageData_ofFormat(v___x_1139_);
v___x_1141_ = l_Lean_throwErrorAt___redArg(v_inst_1023_, v_inst_1024_, v_stx_1025_, v___x_1140_);
return v___x_1141_;
}
else
{
lean_object* v_t_x3f_1142_; lean_object* v___x_1143_; 
v_t_x3f_1142_ = l_Lean_Syntax_getArg(v___x_1124_, v___x_1058_);
lean_dec(v___x_1124_);
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_t_x3f_1142_);
v_t_x3f_1086_ = v___x_1143_;
goto v___jp_1085_;
}
}
else
{
lean_object* v___x_1144_; 
lean_dec(v___x_1124_);
v___x_1144_ = lean_box(0);
v_t_x3f_1086_ = v___x_1144_;
goto v___jp_1085_;
}
v___jp_1059_:
{
lean_object* v___f_1063_; 
lean_inc(v___y_1060_);
lean_inc(v_toBind_1033_);
lean_inc(v_toPure_1035_);
v___f_1063_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19), 15, 14);
lean_closure_set(v___f_1063_, 0, v_stx_1025_);
lean_closure_set(v___f_1063_, 1, v___x_1058_);
lean_closure_set(v___f_1063_, 2, v_toPure_1035_);
lean_closure_set(v___f_1063_, 3, v_d_x3f_1062_);
lean_closure_set(v___f_1063_, 4, v_toBind_1033_);
lean_closure_set(v___f_1063_, 5, v_toFunctor_1034_);
lean_closure_set(v___f_1063_, 6, v___f_1057_);
lean_closure_set(v___f_1063_, 7, v___x_1036_);
lean_closure_set(v___f_1063_, 8, v___x_1037_);
lean_closure_set(v___f_1063_, 9, v___x_1038_);
lean_closure_set(v___f_1063_, 10, v_inst_1023_);
lean_closure_set(v___f_1063_, 11, v_inst_1024_);
lean_closure_set(v___f_1063_, 12, v___y_1061_);
lean_closure_set(v___f_1063_, 13, v___y_1060_);
if (lean_obj_tag(v___y_1060_) == 1)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1080_; 
v_val_1064_ = lean_ctor_get(v___y_1060_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___y_1060_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1066_ = v___y_1060_;
v_isShared_1067_ = v_isSharedCheck_1080_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v___y_1060_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1080_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__8));
lean_inc(v_val_1064_);
v___x_1069_ = l_Lean_Syntax_isOfKind(v_val_1064_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___f_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_del_object(v___x_1066_);
lean_dec(v_val_1064_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1070_, 0, v___f_1063_);
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1071_);
v___x_1073_ = lean_apply_4(v_toBind_1033_, lean_box(0), lean_box(0), v___x_1072_, v___f_1070_);
return v___x_1073_;
}
else
{
lean_object* v___f_1074_; lean_object* v___x_1076_; 
v___f_1074_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1074_, 0, v___f_1063_);
if (v_isShared_1067_ == 0)
{
v___x_1076_ = v___x_1066_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_val_1064_);
v___x_1076_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1076_);
v___x_1078_ = lean_apply_4(v_toBind_1033_, lean_box(0), lean_box(0), v___x_1077_, v___f_1074_);
return v___x_1078_;
}
}
}
}
else
{
lean_object* v___f_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v___y_1060_);
v___f_1081_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1081_, 0, v___f_1063_);
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1082_);
v___x_1084_ = lean_apply_4(v_toBind_1033_, lean_box(0), lean_box(0), v___x_1083_, v___f_1081_);
return v___x_1084_;
}
}
v___jp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = lean_unsigned_to_nat(1u);
v___x_1088_ = l_Lean_Syntax_getArg(v_stx_1025_, v___x_1087_);
v___x_1089_ = l_Lean_Syntax_isNone(v___x_1088_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; 
lean_inc(v___x_1088_);
v___x_1090_ = l_Lean_Syntax_matchesNull(v___x_1088_, v___x_1087_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec(v___x_1088_);
lean_dec(v_t_x3f_1086_);
v___x_1091_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1092_ = lean_box(0);
lean_inc_n(v_stx_1025_, 2);
v___x_1093_ = l_Lean_Syntax_formatStx(v_stx_1025_, v___x_1092_, v___x_1090_);
v___x_1094_ = l_Std_Format_defWidth;
v___x_1095_ = l_Std_Format_pretty(v___x_1093_, v___x_1094_, v___x_1058_, v___x_1058_);
v___x_1096_ = lean_string_append(v___x_1091_, v___x_1095_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1098_ = lean_string_append(v___x_1096_, v___x_1097_);
v___x_1099_ = l_Lean_Syntax_getKind(v_stx_1025_);
v___x_1100_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1099_, v___x_1040_);
v___x_1101_ = lean_string_append(v___x_1098_, v___x_1100_);
lean_dec_ref(v___x_1100_);
v___x_1102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
v___x_1103_ = l_Lean_MessageData_ofFormat(v___x_1102_);
v___x_1104_ = l_Lean_throwErrorAt___redArg(v_inst_1023_, v_inst_1024_, v_stx_1025_, v___x_1103_);
return v___x_1104_;
}
else
{
lean_object* v_d_x3f_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_d_x3f_1105_ = l_Lean_Syntax_getArg(v___x_1088_, v___x_1058_);
lean_dec(v___x_1088_);
v___x_1106_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__9));
lean_inc(v_d_x3f_1105_);
v___x_1107_ = l_Lean_Syntax_isOfKind(v_d_x3f_1105_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v_d_x3f_1105_);
lean_dec(v_t_x3f_1086_);
v___x_1108_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1109_ = lean_box(0);
lean_inc_n(v_stx_1025_, 2);
v___x_1110_ = l_Lean_Syntax_formatStx(v_stx_1025_, v___x_1109_, v___x_1107_);
v___x_1111_ = l_Std_Format_defWidth;
v___x_1112_ = l_Std_Format_pretty(v___x_1110_, v___x_1111_, v___x_1058_, v___x_1058_);
v___x_1113_ = lean_string_append(v___x_1108_, v___x_1112_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1115_ = lean_string_append(v___x_1113_, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_getKind(v_stx_1025_);
v___x_1117_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1116_, v___x_1090_);
v___x_1118_ = lean_string_append(v___x_1115_, v___x_1117_);
lean_dec_ref(v___x_1117_);
v___x_1119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
v___x_1120_ = l_Lean_MessageData_ofFormat(v___x_1119_);
v___x_1121_ = l_Lean_throwErrorAt___redArg(v_inst_1023_, v_inst_1024_, v_stx_1025_, v___x_1120_);
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; 
lean_inc(v_toPure_1035_);
lean_inc_ref(v_toFunctor_1034_);
lean_inc(v_toBind_1033_);
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v_d_x3f_1105_);
v___y_1060_ = v_t_x3f_1086_;
v___y_1061_ = v___x_1087_;
v_d_x3f_1062_ = v___x_1122_;
goto v___jp_1059_;
}
}
}
else
{
lean_object* v___x_1123_; 
lean_inc(v_toPure_1035_);
lean_inc_ref(v_toFunctor_1034_);
lean_inc(v_toBind_1033_);
lean_dec(v___x_1088_);
v___x_1123_ = lean_box(0);
v___y_1060_ = v_t_x3f_1086_;
v___y_1061_ = v___x_1087_;
v_d_x3f_1062_ = v___x_1123_;
goto v___jp_1059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* v_m_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_stx_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Elab_elabTerminationHints___redArg(v_inst_1146_, v_inst_1147_, v_stx_1148_);
return v___x_1149_;
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
