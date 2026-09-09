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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Elab_isInductiveFixpoint(uint8_t v_x_89_){
_start:
{
if (v_x_89_ == 2)
{
uint8_t v___x_90_; 
v___x_90_ = 1;
return v___x_90_;
}
else
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isInductiveFixpoint___boxed(lean_object* v_x_92_){
_start:
{
uint8_t v_x_17__boxed_93_; uint8_t v_res_94_; lean_object* v_r_95_; 
v_x_17__boxed_93_ = lean_unbox(v_x_92_);
v_res_94_ = l_Lean_Elab_isInductiveFixpoint(v_x_17__boxed_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isCoinductiveFixpoint(uint8_t v_x_96_){
_start:
{
if (v_x_96_ == 1)
{
uint8_t v___x_97_; 
v___x_97_ = 1;
return v___x_97_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isCoinductiveFixpoint___boxed(lean_object* v_x_99_){
_start:
{
uint8_t v_x_17__boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_x_17__boxed_100_ = lean_unbox(v_x_99_);
v_res_101_ = l_Lean_Elab_isCoinductiveFixpoint(v_x_17__boxed_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isPartialFixpoint(uint8_t v_x_103_){
_start:
{
if (v_x_103_ == 0)
{
uint8_t v___x_104_; 
v___x_104_ = 1;
return v___x_104_;
}
else
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isPartialFixpoint___boxed(lean_object* v_x_106_){
_start:
{
uint8_t v_x_17__boxed_107_; uint8_t v_res_108_; lean_object* v_r_109_; 
v_x_17__boxed_107_ = lean_unbox(v_x_106_);
v_res_108_ = l_Lean_Elab_isPartialFixpoint(v_x_17__boxed_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isLatticeTheoretic(uint8_t v_p_110_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = l_Lean_Elab_isInductiveFixpoint(v_p_110_);
if (v___x_111_ == 0)
{
uint8_t v___x_112_; 
v___x_112_ = l_Lean_Elab_isCoinductiveFixpoint(v_p_110_);
return v___x_112_;
}
else
{
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isLatticeTheoretic___boxed(lean_object* v_p_113_){
_start:
{
uint8_t v_p_boxed_114_; uint8_t v_res_115_; lean_object* v_r_116_; 
v_p_boxed_114_ = lean_unbox(v_p_113_);
v_res_115_ = l_Lean_Elab_isLatticeTheoretic(v_p_boxed_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_118_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_alloc_ctor(0, 11, 0);
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
lean_object* v___x_141_; lean_object* v_toCold_142_; lean_object* v_env_143_; lean_object* v_options_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_141_ = lean_st_ref_get(v___y_139_);
v_toCold_142_ = lean_ctor_get(v___y_138_, 0);
v_env_143_ = lean_ctor_get(v___x_141_, 0);
lean_inc_ref(v_env_143_);
lean_dec(v___x_141_);
v_options_144_ = lean_ctor_get(v_toCold_142_, 2);
v___x_145_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2);
v___x_146_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_144_);
v___x_147_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_147_, 0, v_env_143_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
lean_ctor_set(v___x_147_, 2, v___x_146_);
lean_ctor_set(v___x_147_, 3, v_options_144_);
v___x_148_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_msgData_137_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v_msgData_150_, v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_154_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_163_, uint8_t v___y_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 1)
{
lean_object* v_pre_166_; 
v_pre_166_ = lean_ctor_get(v_x_165_, 0);
switch(lean_obj_tag(v_pre_166_))
{
case 1:
{
lean_object* v_pre_167_; 
v_pre_167_ = lean_ctor_get(v_pre_166_, 0);
switch(lean_obj_tag(v_pre_167_))
{
case 0:
{
lean_object* v_str_168_; lean_object* v_str_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_str_168_ = lean_ctor_get(v_x_165_, 1);
v_str_169_ = lean_ctor_get(v_pre_166_, 1);
v___x_170_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0));
v___x_171_ = lean_string_dec_eq(v_str_169_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1));
v___x_173_ = lean_string_dec_eq(v_str_169_, v___x_172_);
if (v___x_173_ == 0)
{
return v___x_173_;
}
else
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2));
v___x_175_ = lean_string_dec_eq(v_str_168_, v___x_174_);
if (v___x_175_ == 0)
{
return v___x_175_;
}
else
{
return v_suppressElabErrors_163_;
}
}
}
else
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3));
v___x_177_ = lean_string_dec_eq(v_str_168_, v___x_176_);
if (v___x_177_ == 0)
{
return v___x_177_;
}
else
{
return v_suppressElabErrors_163_;
}
}
}
case 1:
{
lean_object* v_pre_178_; 
v_pre_178_ = lean_ctor_get(v_pre_167_, 0);
if (lean_obj_tag(v_pre_178_) == 0)
{
lean_object* v_str_179_; lean_object* v_str_180_; lean_object* v_str_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_str_179_ = lean_ctor_get(v_x_165_, 1);
v_str_180_ = lean_ctor_get(v_pre_166_, 1);
v_str_181_ = lean_ctor_get(v_pre_167_, 1);
v___x_182_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4));
v___x_183_ = lean_string_dec_eq(v_str_181_, v___x_182_);
if (v___x_183_ == 0)
{
return v___x_183_;
}
else
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5));
v___x_185_ = lean_string_dec_eq(v_str_180_, v___x_184_);
if (v___x_185_ == 0)
{
return v___x_185_;
}
else
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6));
v___x_187_ = lean_string_dec_eq(v_str_179_, v___x_186_);
if (v___x_187_ == 0)
{
return v___x_187_;
}
else
{
return v_suppressElabErrors_163_;
}
}
}
}
else
{
return v___y_164_;
}
}
default: 
{
return v___y_164_;
}
}
}
case 0:
{
lean_object* v_str_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_str_188_ = lean_ctor_get(v_x_165_, 1);
v___x_189_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7));
v___x_190_ = lean_string_dec_eq(v_str_188_, v___x_189_);
if (v___x_190_ == 0)
{
return v___x_190_;
}
else
{
return v_suppressElabErrors_163_;
}
}
default: 
{
return v___y_164_;
}
}
}
else
{
return v___y_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_191_, lean_object* v___y_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_suppressElabErrors_boxed_194_; uint8_t v___y_3341__boxed_195_; uint8_t v_res_196_; lean_object* v_r_197_; 
v_suppressElabErrors_boxed_194_ = lean_unbox(v_suppressElabErrors_191_);
v___y_3341__boxed_195_ = lean_unbox(v___y_192_);
v_res_196_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_194_, v___y_3341__boxed_195_, v_x_193_);
lean_dec(v_x_193_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(lean_object* v_opts_198_, lean_object* v_opt_199_){
_start:
{
lean_object* v_name_200_; lean_object* v_defValue_201_; lean_object* v_map_202_; lean_object* v___x_203_; 
v_name_200_ = lean_ctor_get(v_opt_199_, 0);
v_defValue_201_ = lean_ctor_get(v_opt_199_, 1);
v_map_202_ = lean_ctor_get(v_opts_198_, 0);
v___x_203_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_202_, v_name_200_);
if (lean_obj_tag(v___x_203_) == 0)
{
uint8_t v___x_204_; 
v___x_204_ = lean_unbox(v_defValue_201_);
return v___x_204_;
}
else
{
lean_object* v_val_205_; 
v_val_205_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v___x_203_, 1);
if (lean_obj_tag(v_val_205_) == 1)
{
uint8_t v_v_206_; 
v_v_206_ = lean_ctor_get_uint8(v_val_205_, 0);
lean_dec_ref_known(v_val_205_, 0);
return v_v_206_;
}
else
{
uint8_t v___x_207_; 
lean_dec(v_val_205_);
v___x_207_ = lean_unbox(v_defValue_201_);
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_208_, lean_object* v_opt_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_opts_208_, v_opt_209_);
lean_dec_ref(v_opt_209_);
lean_dec_ref(v_opts_208_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(lean_object* v_ref_213_, lean_object* v_msgData_214_, uint8_t v_severity_215_, uint8_t v_isSilent_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___y_221_; uint8_t v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; uint8_t v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; uint8_t v___y_262_; uint8_t v___y_263_; uint8_t v___y_264_; lean_object* v___y_265_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; uint8_t v___y_287_; uint8_t v___y_288_; uint8_t v___y_289_; lean_object* v___y_290_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; uint8_t v___y_297_; lean_object* v___y_298_; uint8_t v___y_299_; uint8_t v___y_300_; uint8_t v___x_305_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; uint8_t v___y_311_; uint8_t v___y_312_; uint8_t v___y_313_; uint8_t v___y_315_; uint8_t v___x_331_; 
v___x_305_ = 2;
v___x_331_ = l_Lean_instBEqMessageSeverity_beq(v_severity_215_, v___x_305_);
if (v___x_331_ == 0)
{
v___y_315_ = v___x_331_;
goto v___jp_314_;
}
else
{
uint8_t v___x_332_; 
lean_inc_ref(v_msgData_214_);
v___x_332_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_214_);
v___y_315_ = v___x_332_;
goto v___jp_314_;
}
v___jp_220_:
{
lean_object* v___x_230_; lean_object* v_toCold_231_; lean_object* v_currNamespace_232_; lean_object* v_openDecls_233_; lean_object* v_env_234_; lean_object* v_nextMacroScope_235_; lean_object* v_ngen_236_; lean_object* v_auxDeclNGen_237_; lean_object* v_traceState_238_; lean_object* v_cache_239_; lean_object* v_messages_240_; lean_object* v_infoState_241_; lean_object* v_snapshotTasks_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_256_; 
v___x_230_ = lean_st_ref_take(v___y_229_);
v_toCold_231_ = lean_ctor_get(v___y_228_, 0);
v_currNamespace_232_ = lean_ctor_get(v_toCold_231_, 4);
v_openDecls_233_ = lean_ctor_get(v_toCold_231_, 5);
v_env_234_ = lean_ctor_get(v___x_230_, 0);
v_nextMacroScope_235_ = lean_ctor_get(v___x_230_, 1);
v_ngen_236_ = lean_ctor_get(v___x_230_, 2);
v_auxDeclNGen_237_ = lean_ctor_get(v___x_230_, 3);
v_traceState_238_ = lean_ctor_get(v___x_230_, 4);
v_cache_239_ = lean_ctor_get(v___x_230_, 5);
v_messages_240_ = lean_ctor_get(v___x_230_, 6);
v_infoState_241_ = lean_ctor_get(v___x_230_, 7);
v_snapshotTasks_242_ = lean_ctor_get(v___x_230_, 8);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_256_ == 0)
{
v___x_244_ = v___x_230_;
v_isShared_245_ = v_isSharedCheck_256_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_snapshotTasks_242_);
lean_inc(v_infoState_241_);
lean_inc(v_messages_240_);
lean_inc(v_cache_239_);
lean_inc(v_traceState_238_);
lean_inc(v_auxDeclNGen_237_);
lean_inc(v_ngen_236_);
lean_inc(v_nextMacroScope_235_);
lean_inc(v_env_234_);
lean_dec(v___x_230_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_256_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
lean_inc(v_openDecls_233_);
lean_inc(v_currNamespace_232_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v_currNamespace_232_);
lean_ctor_set(v___x_246_, 1, v_openDecls_233_);
v___x_247_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___y_226_);
lean_inc_ref(v___y_227_);
lean_inc_ref(v___y_221_);
v___x_248_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_248_, 0, v___y_221_);
lean_ctor_set(v___x_248_, 1, v___y_224_);
lean_ctor_set(v___x_248_, 2, v___y_223_);
lean_ctor_set(v___x_248_, 3, v___y_227_);
lean_ctor_set(v___x_248_, 4, v___x_247_);
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*5, v___y_222_);
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*5 + 1, v___y_225_);
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*5 + 2, v_isSilent_216_);
v___x_249_ = l_Lean_MessageLog_add(v___x_248_, v_messages_240_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 6, v___x_249_);
v___x_251_ = v___x_244_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_env_234_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_nextMacroScope_235_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_ngen_236_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_auxDeclNGen_237_);
lean_ctor_set(v_reuseFailAlloc_255_, 4, v_traceState_238_);
lean_ctor_set(v_reuseFailAlloc_255_, 5, v_cache_239_);
lean_ctor_set(v_reuseFailAlloc_255_, 6, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_255_, 7, v_infoState_241_);
lean_ctor_set(v_reuseFailAlloc_255_, 8, v_snapshotTasks_242_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_st_ref_put(v___y_229_, v___x_251_);
v___x_253_ = lean_box(0);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
}
v___jp_257_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_281_; 
v___x_266_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_214_);
v___x_267_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v___x_266_, v___y_217_, v___y_218_);
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_281_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_281_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_281_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
lean_inc_ref_n(v___y_261_, 2);
v___x_272_ = l_Lean_FileMap_toPosition(v___y_261_, v___y_259_);
lean_dec(v___y_259_);
v___x_273_ = l_Lean_FileMap_toPosition(v___y_261_, v___y_265_);
lean_dec(v___y_265_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
v___x_275_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0));
if (v___y_264_ == 0)
{
lean_del_object(v___x_270_);
lean_dec_ref(v___y_258_);
v___y_221_ = v___y_260_;
v___y_222_ = v___y_262_;
v___y_223_ = v___x_274_;
v___y_224_ = v___x_272_;
v___y_225_ = v___y_263_;
v___y_226_ = v_a_268_;
v___y_227_ = v___x_275_;
v___y_228_ = v___y_217_;
v___y_229_ = v___y_218_;
goto v___jp_220_;
}
else
{
uint8_t v___x_276_; 
lean_inc(v_a_268_);
v___x_276_ = l_Lean_MessageData_hasTag(v___y_258_, v_a_268_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_279_; 
lean_dec_ref_known(v___x_274_, 1);
lean_dec_ref(v___x_272_);
lean_dec(v_a_268_);
v___x_277_ = lean_box(0);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_277_);
v___x_279_ = v___x_270_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
else
{
lean_del_object(v___x_270_);
v___y_221_ = v___y_260_;
v___y_222_ = v___y_262_;
v___y_223_ = v___x_274_;
v___y_224_ = v___x_272_;
v___y_225_ = v___y_263_;
v___y_226_ = v_a_268_;
v___y_227_ = v___x_275_;
v___y_228_ = v___y_217_;
v___y_229_ = v___y_218_;
goto v___jp_220_;
}
}
}
}
v___jp_282_:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Syntax_getTailPos_x3f(v___y_284_, v___y_287_);
lean_dec(v___y_284_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_inc(v___y_290_);
v___y_258_ = v___y_283_;
v___y_259_ = v___y_290_;
v___y_260_ = v___y_286_;
v___y_261_ = v___y_285_;
v___y_262_ = v___y_287_;
v___y_263_ = v___y_288_;
v___y_264_ = v___y_289_;
v___y_265_ = v___y_290_;
goto v___jp_257_;
}
else
{
lean_object* v_val_292_; 
v_val_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v___x_291_, 1);
v___y_258_ = v___y_283_;
v___y_259_ = v___y_290_;
v___y_260_ = v___y_286_;
v___y_261_ = v___y_285_;
v___y_262_ = v___y_287_;
v___y_263_ = v___y_288_;
v___y_264_ = v___y_289_;
v___y_265_ = v_val_292_;
goto v___jp_257_;
}
}
v___jp_293_:
{
lean_object* v_ref_301_; lean_object* v___x_302_; 
v_ref_301_ = l_Lean_replaceRef(v_ref_213_, v___y_298_);
v___x_302_ = l_Lean_Syntax_getPos_x3f(v_ref_301_, v___y_297_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v___x_303_; 
v___x_303_ = lean_unsigned_to_nat(0u);
v___y_283_ = v___y_294_;
v___y_284_ = v_ref_301_;
v___y_285_ = v___y_296_;
v___y_286_ = v___y_295_;
v___y_287_ = v___y_297_;
v___y_288_ = v___y_300_;
v___y_289_ = v___y_299_;
v___y_290_ = v___x_303_;
goto v___jp_282_;
}
else
{
lean_object* v_val_304_; 
v_val_304_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_val_304_);
lean_dec_ref_known(v___x_302_, 1);
v___y_283_ = v___y_294_;
v___y_284_ = v_ref_301_;
v___y_285_ = v___y_296_;
v___y_286_ = v___y_295_;
v___y_287_ = v___y_297_;
v___y_288_ = v___y_300_;
v___y_289_ = v___y_299_;
v___y_290_ = v_val_304_;
goto v___jp_282_;
}
}
v___jp_306_:
{
if (v___y_313_ == 0)
{
v___y_294_ = v___y_307_;
v___y_295_ = v___y_309_;
v___y_296_ = v___y_308_;
v___y_297_ = v___y_311_;
v___y_298_ = v___y_310_;
v___y_299_ = v___y_312_;
v___y_300_ = v_severity_215_;
goto v___jp_293_;
}
else
{
v___y_294_ = v___y_307_;
v___y_295_ = v___y_309_;
v___y_296_ = v___y_308_;
v___y_297_ = v___y_311_;
v___y_298_ = v___y_310_;
v___y_299_ = v___y_312_;
v___y_300_ = v___x_305_;
goto v___jp_293_;
}
}
v___jp_314_:
{
if (v___y_315_ == 0)
{
lean_object* v_toCold_316_; lean_object* v_ref_317_; uint8_t v_suppressElabErrors_318_; lean_object* v_fileName_319_; lean_object* v_fileMap_320_; lean_object* v_options_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___f_324_; uint8_t v___x_325_; uint8_t v___x_326_; 
v_toCold_316_ = lean_ctor_get(v___y_217_, 0);
v_ref_317_ = lean_ctor_get(v___y_217_, 2);
v_suppressElabErrors_318_ = lean_ctor_get_uint8(v___y_217_, sizeof(void*)*3 + 1);
v_fileName_319_ = lean_ctor_get(v_toCold_316_, 0);
v_fileMap_320_ = lean_ctor_get(v_toCold_316_, 1);
v_options_321_ = lean_ctor_get(v_toCold_316_, 2);
v___x_322_ = lean_box(v_suppressElabErrors_318_);
v___x_323_ = lean_box(v___y_315_);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_324_, 0, v___x_322_);
lean_closure_set(v___f_324_, 1, v___x_323_);
v___x_325_ = 1;
v___x_326_ = l_Lean_instBEqMessageSeverity_beq(v_severity_215_, v___x_325_);
if (v___x_326_ == 0)
{
v___y_307_ = v___f_324_;
v___y_308_ = v_fileMap_320_;
v___y_309_ = v_fileName_319_;
v___y_310_ = v_ref_317_;
v___y_311_ = v___y_315_;
v___y_312_ = v_suppressElabErrors_318_;
v___y_313_ = v___x_326_;
goto v___jp_306_;
}
else
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = l_Lean_warningAsError;
v___x_328_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_options_321_, v___x_327_);
v___y_307_ = v___f_324_;
v___y_308_ = v_fileMap_320_;
v___y_309_ = v_fileName_319_;
v___y_310_ = v_ref_317_;
v___y_311_ = v___y_315_;
v___y_312_ = v_suppressElabErrors_318_;
v___y_313_ = v___x_328_;
goto v___jp_306_;
}
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec_ref(v_msgData_214_);
v___x_329_ = lean_box(0);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___boxed(lean_object* v_ref_333_, lean_object* v_msgData_334_, lean_object* v_severity_335_, lean_object* v_isSilent_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
uint8_t v_severity_boxed_340_; uint8_t v_isSilent_boxed_341_; lean_object* v_res_342_; 
v_severity_boxed_340_ = lean_unbox(v_severity_335_);
v_isSilent_boxed_341_ = lean_unbox(v_isSilent_336_);
v_res_342_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_333_, v_msgData_334_, v_severity_boxed_340_, v_isSilent_boxed_341_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v_ref_333_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(lean_object* v_ref_343_, lean_object* v_msgData_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
uint8_t v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; 
v___x_348_ = 1;
v___x_349_ = 0;
v___x_350_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_343_, v_msgData_344_, v___x_348_, v___x_349_, v___y_345_, v___y_346_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(lean_object* v_ref_351_, lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_351_, v_msgData_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v_ref_351_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__0));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__2));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__4));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__6));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__8));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__10));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__12));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone(lean_object* v_hints_378_, lean_object* v_reason_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_ref_383_; lean_object* v_terminationBy_x3f_x3f_384_; lean_object* v_terminationBy_x3f_385_; lean_object* v_partialFixpoint_x3f_386_; lean_object* v_decreasingBy_x3f_387_; uint8_t v_warnIfRedundant_388_; lean_object* v___y_390_; lean_object* v___y_391_; 
v_ref_383_ = lean_ctor_get(v_hints_378_, 0);
lean_inc(v_ref_383_);
v_terminationBy_x3f_x3f_384_ = lean_ctor_get(v_hints_378_, 1);
lean_inc(v_terminationBy_x3f_x3f_384_);
v_terminationBy_x3f_385_ = lean_ctor_get(v_hints_378_, 2);
lean_inc(v_terminationBy_x3f_385_);
v_partialFixpoint_x3f_386_ = lean_ctor_get(v_hints_378_, 3);
lean_inc(v_partialFixpoint_x3f_386_);
v_decreasingBy_x3f_387_ = lean_ctor_get(v_hints_378_, 4);
lean_inc(v_decreasingBy_x3f_387_);
v_warnIfRedundant_388_ = lean_ctor_get_uint8(v_hints_378_, sizeof(void*)*6);
lean_dec_ref(v_hints_378_);
if (v_warnIfRedundant_388_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec(v_decreasingBy_x3f_387_);
lean_dec(v_partialFixpoint_x3f_386_);
lean_dec(v_terminationBy_x3f_385_);
lean_dec(v_terminationBy_x3f_x3f_384_);
lean_dec(v_ref_383_);
lean_dec_ref(v_reason_379_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_x3f_384_) == 0)
{
if (lean_obj_tag(v_terminationBy_x3f_385_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_387_) == 0)
{
lean_dec(v_ref_383_);
if (lean_obj_tag(v_partialFixpoint_x3f_386_) == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec_ref(v_reason_379_);
v___x_398_ = lean_box(0);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
else
{
lean_object* v_val_400_; uint8_t v_fixpointType_401_; 
v_val_400_ = lean_ctor_get(v_partialFixpoint_x3f_386_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v_partialFixpoint_x3f_386_, 1);
v_fixpointType_401_ = lean_ctor_get_uint8(v_val_400_, sizeof(void*)*2);
switch(v_fixpointType_401_)
{
case 0:
{
lean_object* v_ref_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_ref_402_ = lean_ctor_get(v_val_400_, 0);
lean_inc(v_ref_402_);
lean_dec(v_val_400_);
v___x_403_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__3, &l_Lean_Elab_TerminationHints_ensureNone___closed__3_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3);
v___x_404_ = l_Lean_stringToMessageData(v_reason_379_);
v___x_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_402_, v___x_405_, v_a_380_, v_a_381_);
lean_dec(v_ref_402_);
return v___x_406_;
}
case 1:
{
lean_object* v_ref_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_ref_407_ = lean_ctor_get(v_val_400_, 0);
lean_inc(v_ref_407_);
lean_dec(v_val_400_);
v___x_408_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__5, &l_Lean_Elab_TerminationHints_ensureNone___closed__5_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5);
v___x_409_ = l_Lean_stringToMessageData(v_reason_379_);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_407_, v___x_410_, v_a_380_, v_a_381_);
lean_dec(v_ref_407_);
return v___x_411_;
}
default: 
{
lean_object* v_ref_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_ref_412_ = lean_ctor_get(v_val_400_, 0);
lean_inc(v_ref_412_);
lean_dec(v_val_400_);
v___x_413_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__7, &l_Lean_Elab_TerminationHints_ensureNone___closed__7_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7);
v___x_414_ = l_Lean_stringToMessageData(v_reason_379_);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_412_, v___x_415_, v_a_380_, v_a_381_);
lean_dec(v_ref_412_);
return v___x_416_;
}
}
}
}
else
{
if (lean_obj_tag(v_partialFixpoint_x3f_386_) == 0)
{
lean_object* v_val_417_; lean_object* v_ref_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_428_; 
lean_dec(v_ref_383_);
v_val_417_ = lean_ctor_get(v_decreasingBy_x3f_387_, 0);
lean_inc(v_val_417_);
lean_dec_ref_known(v_decreasingBy_x3f_387_, 1);
v_ref_418_ = lean_ctor_get(v_val_417_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v_val_417_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v_val_417_, 1);
lean_dec(v_unused_429_);
v___x_420_ = v_val_417_;
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_ref_418_);
lean_dec(v_val_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_422_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__9, &l_Lean_Elab_TerminationHints_ensureNone___closed__9_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9);
v___x_423_ = l_Lean_stringToMessageData(v_reason_379_);
if (v_isShared_421_ == 0)
{
lean_ctor_set_tag(v___x_420_, 7);
lean_ctor_set(v___x_420_, 1, v___x_423_);
lean_ctor_set(v___x_420_, 0, v___x_422_);
v___x_425_ = v___x_420_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_423_);
v___x_425_ = v_reuseFailAlloc_427_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_418_, v___x_425_, v_a_380_, v_a_381_);
lean_dec(v_ref_418_);
return v___x_426_;
}
}
}
else
{
lean_dec_ref_known(v_decreasingBy_x3f_387_, 1);
lean_dec(v_partialFixpoint_x3f_386_);
v___y_390_ = v_a_380_;
v___y_391_ = v_a_381_;
goto v___jp_389_;
}
}
}
else
{
if (lean_obj_tag(v_decreasingBy_x3f_387_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_386_) == 0)
{
lean_object* v_val_430_; lean_object* v_ref_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v_ref_383_);
v_val_430_ = lean_ctor_get(v_terminationBy_x3f_385_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v_terminationBy_x3f_385_, 1);
v_ref_431_ = lean_ctor_get(v_val_430_, 0);
lean_inc(v_ref_431_);
lean_dec(v_val_430_);
v___x_432_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__11, &l_Lean_Elab_TerminationHints_ensureNone___closed__11_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11);
v___x_433_ = l_Lean_stringToMessageData(v_reason_379_);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_431_, v___x_434_, v_a_380_, v_a_381_);
lean_dec(v_ref_431_);
return v___x_435_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_385_, 1);
lean_dec(v_partialFixpoint_x3f_386_);
v___y_390_ = v_a_380_;
v___y_391_ = v_a_381_;
goto v___jp_389_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_385_, 1);
lean_dec(v_decreasingBy_x3f_387_);
lean_dec(v_partialFixpoint_x3f_386_);
v___y_390_ = v_a_380_;
v___y_391_ = v_a_381_;
goto v___jp_389_;
}
}
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_385_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_387_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_386_) == 0)
{
lean_object* v_val_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec(v_ref_383_);
v_val_436_ = lean_ctor_get(v_terminationBy_x3f_x3f_384_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_384_, 1);
v___x_437_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__13, &l_Lean_Elab_TerminationHints_ensureNone___closed__13_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13);
v___x_438_ = l_Lean_stringToMessageData(v_reason_379_);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_val_436_, v___x_439_, v_a_380_, v_a_381_);
lean_dec(v_val_436_);
return v___x_440_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_384_, 1);
lean_dec(v_partialFixpoint_x3f_386_);
v___y_390_ = v_a_380_;
v___y_391_ = v_a_381_;
goto v___jp_389_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_384_, 1);
lean_dec(v_decreasingBy_x3f_387_);
lean_dec(v_partialFixpoint_x3f_386_);
v___y_390_ = v_a_380_;
v___y_391_ = v_a_381_;
goto v___jp_389_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_384_, 1);
lean_dec(v_decreasingBy_x3f_387_);
lean_dec(v_partialFixpoint_x3f_386_);
lean_dec(v_terminationBy_x3f_385_);
v___y_390_ = v_a_380_;
v___y_391_ = v_a_381_;
goto v___jp_389_;
}
}
}
v___jp_389_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__1, &l_Lean_Elab_TerminationHints_ensureNone___closed__1_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1);
v___x_393_ = l_Lean_stringToMessageData(v_reason_379_);
v___x_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_383_, v___x_394_, v___y_390_, v___y_391_);
lean_dec(v_ref_383_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone___boxed(lean_object* v_hints_441_, lean_object* v_reason_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Elab_TerminationHints_ensureNone(v_hints_441_, v_reason_442_, v_a_443_, v_a_444_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
return v_res_446_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_TerminationHints_isNotNone(lean_object* v_hints_447_){
_start:
{
lean_object* v_terminationBy_x3f_x3f_448_; 
v_terminationBy_x3f_x3f_448_ = lean_ctor_get(v_hints_447_, 1);
if (lean_obj_tag(v_terminationBy_x3f_x3f_448_) == 0)
{
lean_object* v_terminationBy_x3f_449_; 
v_terminationBy_x3f_449_ = lean_ctor_get(v_hints_447_, 2);
if (lean_obj_tag(v_terminationBy_x3f_449_) == 0)
{
lean_object* v_decreasingBy_x3f_450_; 
v_decreasingBy_x3f_450_ = lean_ctor_get(v_hints_447_, 4);
if (lean_obj_tag(v_decreasingBy_x3f_450_) == 0)
{
lean_object* v_partialFixpoint_x3f_451_; 
v_partialFixpoint_x3f_451_ = lean_ctor_get(v_hints_447_, 3);
if (lean_obj_tag(v_partialFixpoint_x3f_451_) == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
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
else
{
uint8_t v___x_455_; 
v___x_455_ = 1;
return v___x_455_;
}
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 1;
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_isNotNone___boxed(lean_object* v_hints_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Lean_Elab_TerminationHints_isNotNone(v_hints_457_);
lean_dec_ref(v_hints_457_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object* v_headerParams_460_, lean_object* v_hints_461_, lean_object* v_value_462_){
_start:
{
lean_object* v_ref_463_; lean_object* v_terminationBy_x3f_x3f_464_; lean_object* v_terminationBy_x3f_465_; lean_object* v_partialFixpoint_x3f_466_; lean_object* v_decreasingBy_x3f_467_; uint8_t v_warnIfRedundant_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_477_; 
v_ref_463_ = lean_ctor_get(v_hints_461_, 0);
v_terminationBy_x3f_x3f_464_ = lean_ctor_get(v_hints_461_, 1);
v_terminationBy_x3f_465_ = lean_ctor_get(v_hints_461_, 2);
v_partialFixpoint_x3f_466_ = lean_ctor_get(v_hints_461_, 3);
v_decreasingBy_x3f_467_ = lean_ctor_get(v_hints_461_, 4);
v_warnIfRedundant_468_ = lean_ctor_get_uint8(v_hints_461_, sizeof(void*)*6);
v_isSharedCheck_477_ = !lean_is_exclusive(v_hints_461_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_hints_461_, 5);
lean_dec(v_unused_478_);
v___x_470_ = v_hints_461_;
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_decreasingBy_x3f_467_);
lean_inc(v_partialFixpoint_x3f_466_);
lean_inc(v_terminationBy_x3f_465_);
lean_inc(v_terminationBy_x3f_x3f_464_);
lean_inc(v_ref_463_);
lean_dec(v_hints_461_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = l_Lean_Expr_getNumHeadLambdas(v_value_462_);
v___x_473_ = lean_nat_sub(v___x_472_, v_headerParams_460_);
lean_dec(v___x_472_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 5, v___x_473_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_ref_463_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_terminationBy_x3f_x3f_464_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_terminationBy_x3f_465_);
lean_ctor_set(v_reuseFailAlloc_476_, 3, v_partialFixpoint_x3f_466_);
lean_ctor_set(v_reuseFailAlloc_476_, 4, v_decreasingBy_x3f_467_);
lean_ctor_set(v_reuseFailAlloc_476_, 5, v___x_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_476_, sizeof(void*)*6, v_warnIfRedundant_468_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(lean_object* v_headerParams_479_, lean_object* v_hints_480_, lean_object* v_value_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v_headerParams_479_, v_hints_480_, v_value_481_);
lean_dec_ref(v_value_481_);
lean_dec(v_headerParams_479_);
return v_res_482_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3));
v___x_490_ = l_Lean_MessageData_ofFormat(v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(lean_object* v_a_491_){
_start:
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_nat_dec_eq(v_a_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_494_ = l_Nat_reprFast(v_a_491_);
v___x_495_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
v___x_496_ = l_Lean_MessageData_ofFormat(v___x_495_);
v___x_497_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
lean_dec(v_a_491_);
v___x_499_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(lean_object* v_msgData_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; lean_object* v_env_507_; lean_object* v___x_508_; lean_object* v_toCold_509_; lean_object* v_mctx_510_; lean_object* v_lctx_511_; lean_object* v_options_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_506_ = lean_st_ref_get(v___y_504_);
v_env_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_env_507_);
lean_dec(v___x_506_);
v___x_508_ = lean_st_ref_get(v___y_502_);
v_toCold_509_ = lean_ctor_get(v___y_503_, 0);
v_mctx_510_ = lean_ctor_get(v___x_508_, 0);
lean_inc_ref(v_mctx_510_);
lean_dec(v___x_508_);
v_lctx_511_ = lean_ctor_get(v___y_501_, 2);
v_options_512_ = lean_ctor_get(v_toCold_509_, 2);
lean_inc_ref(v_options_512_);
lean_inc_ref(v_lctx_511_);
v___x_513_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_513_, 0, v_env_507_);
lean_ctor_set(v___x_513_, 1, v_mctx_510_);
lean_ctor_set(v___x_513_, 2, v_lctx_511_);
lean_ctor_set(v___x_513_, 3, v_options_512_);
v___x_514_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v_msgData_500_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(lean_object* v_msg_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_ref_529_; lean_object* v___x_530_; lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_539_; 
v_ref_529_ = lean_ctor_get(v___y_526_, 2);
v___x_530_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msg_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_539_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
lean_inc(v_ref_529_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_ref_529_);
lean_ctor_set(v___x_535_, 1, v_a_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 1);
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_msg_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object* v_ref_547_, lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_toCold_554_; lean_object* v_currRecDepth_555_; lean_object* v_ref_556_; uint8_t v_diag_557_; uint8_t v_suppressElabErrors_558_; lean_object* v_ref_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_toCold_554_ = lean_ctor_get(v___y_551_, 0);
v_currRecDepth_555_ = lean_ctor_get(v___y_551_, 1);
v_ref_556_ = lean_ctor_get(v___y_551_, 2);
v_diag_557_ = lean_ctor_get_uint8(v___y_551_, sizeof(void*)*3);
v_suppressElabErrors_558_ = lean_ctor_get_uint8(v___y_551_, sizeof(void*)*3 + 1);
v_ref_559_ = l_Lean_replaceRef(v_ref_547_, v_ref_556_);
lean_inc(v_currRecDepth_555_);
lean_inc_ref(v_toCold_554_);
v___x_560_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_560_, 0, v_toCold_554_);
lean_ctor_set(v___x_560_, 1, v_currRecDepth_555_);
lean_ctor_set(v___x_560_, 2, v_ref_559_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*3, v_diag_557_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*3 + 1, v_suppressElabErrors_558_);
v___x_561_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_548_, v___y_549_, v___y_550_, v___x_560_, v___y_552_);
lean_dec_ref_known(v___x_560_, 3);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object* v_ref_562_, lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_562_, v_msg_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v_ref_562_);
return v_res_569_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__0));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__3(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__2));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__5(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__4));
v___x_578_ = l_Lean_stringToMessageData(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__9(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__8));
v___x_584_ = l_Lean_stringToMessageData(v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__12(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__11));
v___x_589_ = l_Lean_MessageData_ofFormat(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object* v_funName_590_, lean_object* v_extraParams_591_, lean_object* v_tb_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
uint8_t v_synthetic_598_; 
v_synthetic_598_ = lean_ctor_get_uint8(v_tb_592_, sizeof(void*)*3 + 1);
if (v_synthetic_598_ == 0)
{
lean_object* v_ref_599_; lean_object* v_vars_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_ref_599_ = lean_ctor_get(v_tb_592_, 0);
v_vars_600_ = lean_ctor_get(v_tb_592_, 1);
v___x_601_ = lean_array_get_size(v_vars_600_);
v___x_602_ = lean_nat_dec_lt(v_extraParams_591_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v_extraParams_591_);
lean_dec(v_funName_590_);
v___x_603_ = lean_box(0);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_msg_615_; lean_object* v___x_616_; lean_object* v_ident_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_605_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_601_);
v___x_606_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__1, &l_Lean_Elab_TerminationBy_checkVars___closed__1_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__1);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
lean_inc(v_funName_590_);
v___x_608_ = l_Lean_MessageData_ofName(v_funName_590_);
v___x_609_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__3, &l_Lean_Elab_TerminationBy_checkVars___closed__3_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__3);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_591_);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__5, &l_Lean_Elab_TerminationBy_checkVars___closed__5_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__5);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v_msg_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_615_, 0, v___x_607_);
lean_ctor_set(v_msg_615_, 1, v___x_614_);
v___x_616_ = lean_unsigned_to_nat(0u);
v_ident_617_ = lean_array_fget_borrowed(v_vars_600_, v___x_616_);
v___x_618_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__7));
lean_inc(v_ident_617_);
v___x_619_ = l_Lean_Syntax_isOfKind(v_ident_617_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec(v_funName_590_);
v___x_620_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_599_, v_msg_615_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = l_Lean_TSyntax_getId(v_ident_617_);
v___x_622_ = l_Lean_Name_isSuffixOf(v___x_621_, v_funName_590_);
lean_dec(v_funName_590_);
lean_dec(v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_599_, v_msg_615_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_msg_627_; lean_object* v___x_628_; 
v___x_624_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__9, &l_Lean_Elab_TerminationBy_checkVars___closed__9_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__9);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v_msg_615_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__12, &l_Lean_Elab_TerminationBy_checkVars___closed__12_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__12);
v_msg_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_627_, 0, v___x_625_);
lean_ctor_set(v_msg_627_, 1, v___x_626_);
v___x_628_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_599_, v_msg_627_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
return v___x_628_;
}
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec(v_extraParams_591_);
lean_dec(v_funName_590_);
v___x_629_ = lean_box(0);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object* v_funName_631_, lean_object* v_extraParams_632_, lean_object* v_tb_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Elab_TerminationBy_checkVars(v_funName_631_, v_extraParams_632_, v_tb_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec_ref(v_tb_633_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_object* v_00_u03b1_640_, lean_object* v_ref_641_, lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_641_, v_msg_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object* v_00_u03b1_649_, lean_object* v_ref_650_, lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(v_00_u03b1_649_, v_ref_650_, v_msg_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v_ref_650_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_object* v_00_u03b1_658_, lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_666_, lean_object* v_msg_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_666_, v_msg_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object* v_val_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v_val_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object* v_stx_676_, lean_object* v_terminationBy_x3f_x3f_677_, lean_object* v_terminationBy_x3f_678_, lean_object* v_partialFixpoint_x3f_679_, lean_object* v___x_680_, uint8_t v___x_681_, lean_object* v_toPure_682_, lean_object* v_decreasingBy_x3f_683_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_684_, 0, v_stx_676_);
lean_ctor_set(v___x_684_, 1, v_terminationBy_x3f_x3f_677_);
lean_ctor_set(v___x_684_, 2, v_terminationBy_x3f_678_);
lean_ctor_set(v___x_684_, 3, v_partialFixpoint_x3f_679_);
lean_ctor_set(v___x_684_, 4, v_decreasingBy_x3f_683_);
lean_ctor_set(v___x_684_, 5, v___x_680_);
lean_ctor_set_uint8(v___x_684_, sizeof(void*)*6, v___x_681_);
v___x_685_ = lean_apply_2(v_toPure_682_, lean_box(0), v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed(lean_object* v_stx_686_, lean_object* v_terminationBy_x3f_x3f_687_, lean_object* v_terminationBy_x3f_688_, lean_object* v_partialFixpoint_x3f_689_, lean_object* v___x_690_, lean_object* v___x_691_, lean_object* v_toPure_692_, lean_object* v_decreasingBy_x3f_693_){
_start:
{
uint8_t v___x_2901__boxed_694_; lean_object* v_res_695_; 
v___x_2901__boxed_694_ = lean_unbox(v___x_691_);
v_res_695_ = l_Lean_Elab_elabTerminationHints___redArg___lam__1(v_stx_686_, v_terminationBy_x3f_x3f_687_, v_terminationBy_x3f_688_, v_partialFixpoint_x3f_689_, v___x_690_, v___x_2901__boxed_694_, v_toPure_692_, v_decreasingBy_x3f_693_);
return v_res_695_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* v_stx_700_, lean_object* v_terminationBy_x3f_x3f_701_, lean_object* v_terminationBy_x3f_702_, lean_object* v___x_703_, uint8_t v___x_704_, lean_object* v_toPure_705_, lean_object* v_d_x3f_706_, lean_object* v_toBind_707_, lean_object* v_toFunctor_708_, lean_object* v___f_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v___x_715_, lean_object* v_partialFixpoint_x3f_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___f_718_; 
v___x_717_ = lean_box(v___x_704_);
lean_inc(v_toPure_705_);
v___f_718_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_718_, 0, v_stx_700_);
lean_closure_set(v___f_718_, 1, v_terminationBy_x3f_x3f_701_);
lean_closure_set(v___f_718_, 2, v_terminationBy_x3f_702_);
lean_closure_set(v___f_718_, 3, v_partialFixpoint_x3f_716_);
lean_closure_set(v___f_718_, 4, v___x_703_);
lean_closure_set(v___f_718_, 5, v___x_717_);
lean_closure_set(v___f_718_, 6, v_toPure_705_);
if (lean_obj_tag(v_d_x3f_706_) == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec_ref(v_inst_714_);
lean_dec_ref(v_inst_713_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v___f_709_);
lean_dec_ref(v_toFunctor_708_);
v___x_719_ = lean_box(0);
v___x_720_ = lean_apply_2(v_toPure_705_, lean_box(0), v___x_719_);
v___x_721_ = lean_apply_4(v_toBind_707_, lean_box(0), lean_box(0), v___x_720_, v___f_718_);
return v___x_721_;
}
else
{
lean_object* v_val_722_; lean_object* v_map_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_741_; 
v_val_722_ = lean_ctor_get(v_d_x3f_706_, 0);
lean_inc(v_val_722_);
lean_dec_ref_known(v_d_x3f_706_, 1);
v_map_723_ = lean_ctor_get(v_toFunctor_708_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_toFunctor_708_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_toFunctor_708_, 1);
lean_dec(v_unused_742_);
v___x_725_ = v_toFunctor_708_;
v_isShared_726_ = v_isSharedCheck_741_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_map_723_);
lean_dec(v_toFunctor_708_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_741_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___y_728_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0));
v___x_732_ = l_Lean_Name_mkStr4(v___x_710_, v___x_711_, v___x_712_, v___x_731_);
lean_inc(v_val_722_);
v___x_733_ = l_Lean_Syntax_isOfKind(v_val_722_, v___x_732_);
lean_dec(v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_del_object(v___x_725_);
lean_dec(v_toPure_705_);
v___x_734_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2, &l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2);
v___x_735_ = l_Lean_throwErrorAt___redArg(v_inst_713_, v_inst_714_, v_val_722_, v___x_734_);
v___y_728_ = v___x_735_;
goto v___jp_727_;
}
else
{
lean_object* v_tactic_736_; lean_object* v___x_738_; 
lean_dec_ref(v_inst_714_);
lean_dec_ref(v_inst_713_);
v_tactic_736_ = l_Lean_Syntax_getArg(v_val_722_, v___x_715_);
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
v___x_739_ = lean_apply_2(v_toPure_705_, lean_box(0), v___x_738_);
v___y_728_ = v___x_739_;
goto v___jp_727_;
}
}
v___jp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_apply_4(v_map_723_, lean_box(0), lean_box(0), v___f_709_, v___y_728_);
v___x_730_ = lean_apply_4(v_toBind_707_, lean_box(0), lean_box(0), v___x_729_, v___f_718_);
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_stx_743_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_744_ = _args[1];
lean_object* v_terminationBy_x3f_745_ = _args[2];
lean_object* v___x_746_ = _args[3];
lean_object* v___x_747_ = _args[4];
lean_object* v_toPure_748_ = _args[5];
lean_object* v_d_x3f_749_ = _args[6];
lean_object* v_toBind_750_ = _args[7];
lean_object* v_toFunctor_751_ = _args[8];
lean_object* v___f_752_ = _args[9];
lean_object* v___x_753_ = _args[10];
lean_object* v___x_754_ = _args[11];
lean_object* v___x_755_ = _args[12];
lean_object* v_inst_756_ = _args[13];
lean_object* v_inst_757_ = _args[14];
lean_object* v___x_758_ = _args[15];
lean_object* v_partialFixpoint_x3f_759_ = _args[16];
_start:
{
uint8_t v___x_2919__boxed_760_; lean_object* v_res_761_; 
v___x_2919__boxed_760_ = lean_unbox(v___x_747_);
v_res_761_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_743_, v_terminationBy_x3f_x3f_744_, v_terminationBy_x3f_745_, v___x_746_, v___x_2919__boxed_760_, v_toPure_748_, v_d_x3f_749_, v_toBind_750_, v_toFunctor_751_, v___f_752_, v___x_753_, v___x_754_, v___x_755_, v_inst_756_, v_inst_757_, v___x_758_, v_partialFixpoint_x3f_759_);
lean_dec(v___x_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object* v___f_762_, lean_object* v_partialFixpoint_x3f_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = lean_apply_1(v___f_762_, v_partialFixpoint_x3f_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object* v_stx_768_, lean_object* v_terminationBy_x3f_x3f_769_, lean_object* v___x_770_, uint8_t v___x_771_, lean_object* v_toPure_772_, lean_object* v_d_x3f_773_, lean_object* v_toBind_774_, lean_object* v_toFunctor_775_, lean_object* v___f_776_, lean_object* v___x_777_, lean_object* v___x_778_, lean_object* v___x_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v___x_782_, lean_object* v_t_x3f_783_, lean_object* v_terminationBy_x3f_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___f_786_; 
v___x_785_ = lean_box(v___x_771_);
lean_inc(v___x_782_);
lean_inc_ref(v___x_779_);
lean_inc_ref(v___x_778_);
lean_inc_ref(v___x_777_);
lean_inc(v_toBind_774_);
lean_inc(v_toPure_772_);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed), 17, 16);
lean_closure_set(v___f_786_, 0, v_stx_768_);
lean_closure_set(v___f_786_, 1, v_terminationBy_x3f_x3f_769_);
lean_closure_set(v___f_786_, 2, v_terminationBy_x3f_784_);
lean_closure_set(v___f_786_, 3, v___x_770_);
lean_closure_set(v___f_786_, 4, v___x_785_);
lean_closure_set(v___f_786_, 5, v_toPure_772_);
lean_closure_set(v___f_786_, 6, v_d_x3f_773_);
lean_closure_set(v___f_786_, 7, v_toBind_774_);
lean_closure_set(v___f_786_, 8, v_toFunctor_775_);
lean_closure_set(v___f_786_, 9, v___f_776_);
lean_closure_set(v___f_786_, 10, v___x_777_);
lean_closure_set(v___f_786_, 11, v___x_778_);
lean_closure_set(v___f_786_, 12, v___x_779_);
lean_closure_set(v___f_786_, 13, v_inst_780_);
lean_closure_set(v___f_786_, 14, v_inst_781_);
lean_closure_set(v___f_786_, 15, v___x_782_);
if (lean_obj_tag(v_t_x3f_783_) == 1)
{
lean_object* v_val_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_864_; 
v_val_787_ = lean_ctor_get(v_t_x3f_783_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v_t_x3f_783_);
if (v_isSharedCheck_864_ == 0)
{
v___x_789_ = v_t_x3f_783_;
v_isShared_790_ = v_isSharedCheck_864_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_val_787_);
lean_dec(v_t_x3f_783_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_864_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_791_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_779_);
lean_inc_ref(v___x_778_);
lean_inc_ref(v___x_777_);
v___x_792_ = l_Lean_Name_mkStr4(v___x_777_, v___x_778_, v___x_779_, v___x_791_);
lean_inc(v_val_787_);
v___x_793_ = l_Lean_Syntax_isOfKind(v_val_787_, v___x_792_);
lean_dec(v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_794_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_779_);
lean_inc_ref(v___x_778_);
lean_inc_ref(v___x_777_);
v___x_795_ = l_Lean_Name_mkStr4(v___x_777_, v___x_778_, v___x_779_, v___x_794_);
lean_inc(v_val_787_);
v___x_796_ = l_Lean_Syntax_isOfKind(v_val_787_, v___x_795_);
lean_dec(v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_797_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_798_ = l_Lean_Name_mkStr4(v___x_777_, v___x_778_, v___x_779_, v___x_797_);
lean_inc(v_val_787_);
v___x_799_ = l_Lean_Syntax_isOfKind(v_val_787_, v___x_798_);
lean_dec(v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___f_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_del_object(v___x_789_);
lean_dec(v_val_787_);
lean_dec(v___x_782_);
v___f_800_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_800_, 0, v___f_786_);
v___x_801_ = lean_box(0);
v___x_802_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_801_);
v___x_803_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_802_, v___f_800_);
return v___x_803_;
}
else
{
lean_object* v___f_804_; lean_object* v_term_x3f_806_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___f_804_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_804_, 0, v___f_786_);
v___x_814_ = l_Lean_Syntax_getArg(v_val_787_, v___x_782_);
v___x_815_ = l_Lean_Syntax_isNone(v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_814_);
v___x_817_ = l_Lean_Syntax_matchesNull(v___x_814_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec(v___x_814_);
lean_del_object(v___x_789_);
lean_dec(v_val_787_);
lean_dec(v___x_782_);
v___x_818_ = lean_box(0);
v___x_819_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_818_);
v___x_820_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_819_, v___f_804_);
return v___x_820_;
}
else
{
lean_object* v_term_x3f_821_; lean_object* v___x_822_; 
v_term_x3f_821_ = l_Lean_Syntax_getArg(v___x_814_, v___x_782_);
lean_dec(v___x_782_);
lean_dec(v___x_814_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_term_x3f_821_);
v_term_x3f_806_ = v___x_822_;
goto v___jp_805_;
}
}
else
{
lean_object* v___x_823_; 
lean_dec(v___x_814_);
lean_dec(v___x_782_);
v___x_823_ = lean_box(0);
v_term_x3f_806_ = v___x_823_;
goto v___jp_805_;
}
v___jp_805_:
{
uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_807_ = 2;
v___x_808_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_808_, 0, v_val_787_);
lean_ctor_set(v___x_808_, 1, v_term_x3f_806_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*2, v___x_807_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_808_);
v___x_810_ = v___x_789_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_813_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_810_);
v___x_812_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_811_, v___f_804_);
return v___x_812_;
}
}
}
}
else
{
lean_object* v___f_824_; lean_object* v_term_x3f_826_; lean_object* v___x_834_; uint8_t v___x_835_; 
lean_dec_ref(v___x_779_);
lean_dec_ref(v___x_778_);
lean_dec_ref(v___x_777_);
v___f_824_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_824_, 0, v___f_786_);
v___x_834_ = l_Lean_Syntax_getArg(v_val_787_, v___x_782_);
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
lean_del_object(v___x_789_);
lean_dec(v_val_787_);
lean_dec(v___x_782_);
v___x_838_ = lean_box(0);
v___x_839_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_838_);
v___x_840_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_839_, v___f_824_);
return v___x_840_;
}
else
{
lean_object* v_term_x3f_841_; lean_object* v___x_842_; 
v_term_x3f_841_ = l_Lean_Syntax_getArg(v___x_834_, v___x_782_);
lean_dec(v___x_782_);
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
lean_dec(v___x_782_);
v___x_843_ = lean_box(0);
v_term_x3f_826_ = v___x_843_;
goto v___jp_825_;
}
v___jp_825_:
{
uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = 1;
v___x_828_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_828_, 0, v_val_787_);
lean_ctor_set(v___x_828_, 1, v_term_x3f_826_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*2, v___x_827_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_828_);
v___x_830_ = v___x_789_;
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
v___x_831_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_830_);
v___x_832_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_831_, v___f_824_);
return v___x_832_;
}
}
}
}
else
{
lean_object* v___f_844_; lean_object* v_term_x3f_846_; lean_object* v___x_854_; uint8_t v___x_855_; 
lean_dec_ref(v___x_779_);
lean_dec_ref(v___x_778_);
lean_dec_ref(v___x_777_);
v___f_844_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_844_, 0, v___f_786_);
v___x_854_ = l_Lean_Syntax_getArg(v_val_787_, v___x_782_);
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
lean_del_object(v___x_789_);
lean_dec(v_val_787_);
lean_dec(v___x_782_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_858_);
v___x_860_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_859_, v___f_844_);
return v___x_860_;
}
else
{
lean_object* v_term_x3f_861_; lean_object* v___x_862_; 
v_term_x3f_861_ = l_Lean_Syntax_getArg(v___x_854_, v___x_782_);
lean_dec(v___x_782_);
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
lean_dec(v___x_782_);
v___x_863_ = lean_box(0);
v_term_x3f_846_ = v___x_863_;
goto v___jp_845_;
}
v___jp_845_:
{
uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_847_ = 0;
v___x_848_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_848_, 0, v_val_787_);
lean_ctor_set(v___x_848_, 1, v_term_x3f_846_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*2, v___x_847_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_848_);
v___x_850_ = v___x_789_;
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
v___x_851_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_850_);
v___x_852_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_851_, v___f_844_);
return v___x_852_;
}
}
}
}
}
else
{
lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec(v_t_x3f_783_);
lean_dec(v___x_782_);
lean_dec_ref(v___x_779_);
lean_dec_ref(v___x_778_);
lean_dec_ref(v___x_777_);
v___f_865_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_865_, 0, v___f_786_);
v___x_866_ = lean_box(0);
v___x_867_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_866_);
v___x_868_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_867_, v___f_865_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_stx_869_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_870_ = _args[1];
lean_object* v___x_871_ = _args[2];
lean_object* v___x_872_ = _args[3];
lean_object* v_toPure_873_ = _args[4];
lean_object* v_d_x3f_874_ = _args[5];
lean_object* v_toBind_875_ = _args[6];
lean_object* v_toFunctor_876_ = _args[7];
lean_object* v___f_877_ = _args[8];
lean_object* v___x_878_ = _args[9];
lean_object* v___x_879_ = _args[10];
lean_object* v___x_880_ = _args[11];
lean_object* v_inst_881_ = _args[12];
lean_object* v_inst_882_ = _args[13];
lean_object* v___x_883_ = _args[14];
lean_object* v_t_x3f_884_ = _args[15];
lean_object* v_terminationBy_x3f_885_ = _args[16];
_start:
{
uint8_t v___x_3008__boxed_886_; lean_object* v_res_887_; 
v___x_3008__boxed_886_ = lean_unbox(v___x_872_);
v_res_887_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11(v_stx_869_, v_terminationBy_x3f_x3f_870_, v___x_871_, v___x_3008__boxed_886_, v_toPure_873_, v_d_x3f_874_, v_toBind_875_, v_toFunctor_876_, v___f_877_, v___x_878_, v___x_879_, v___x_880_, v_inst_881_, v_inst_882_, v___x_883_, v_t_x3f_884_, v_terminationBy_x3f_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* v___f_888_, lean_object* v_terminationBy_x3f_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = lean_apply_1(v___f_888_, v_terminationBy_x3f_889_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2));
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4));
v___x_898_ = l_Lean_stringToMessageData(v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* v_stx_899_, lean_object* v___x_900_, uint8_t v___x_901_, lean_object* v_toPure_902_, lean_object* v_d_x3f_903_, lean_object* v_toBind_904_, lean_object* v_toFunctor_905_, lean_object* v___f_906_, lean_object* v___x_907_, lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v___x_912_, lean_object* v_t_x3f_913_, lean_object* v_terminationBy_x3f_x3f_914_){
_start:
{
lean_object* v___x_915_; lean_object* v___f_916_; 
v___x_915_ = lean_box(v___x_901_);
lean_inc(v_t_x3f_913_);
lean_inc(v___x_912_);
lean_inc_ref(v_inst_911_);
lean_inc_ref(v_inst_910_);
lean_inc_ref(v___x_909_);
lean_inc_ref(v___x_908_);
lean_inc_ref(v___x_907_);
lean_inc(v_toBind_904_);
lean_inc(v_toPure_902_);
lean_inc(v___x_900_);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_916_, 0, v_stx_899_);
lean_closure_set(v___f_916_, 1, v_terminationBy_x3f_x3f_914_);
lean_closure_set(v___f_916_, 2, v___x_900_);
lean_closure_set(v___f_916_, 3, v___x_915_);
lean_closure_set(v___f_916_, 4, v_toPure_902_);
lean_closure_set(v___f_916_, 5, v_d_x3f_903_);
lean_closure_set(v___f_916_, 6, v_toBind_904_);
lean_closure_set(v___f_916_, 7, v_toFunctor_905_);
lean_closure_set(v___f_916_, 8, v___f_906_);
lean_closure_set(v___f_916_, 9, v___x_907_);
lean_closure_set(v___f_916_, 10, v___x_908_);
lean_closure_set(v___f_916_, 11, v___x_909_);
lean_closure_set(v___f_916_, 12, v_inst_910_);
lean_closure_set(v___f_916_, 13, v_inst_911_);
lean_closure_set(v___f_916_, 14, v___x_912_);
lean_closure_set(v___f_916_, 15, v_t_x3f_913_);
if (lean_obj_tag(v_t_x3f_913_) == 1)
{
lean_object* v_val_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_1029_; 
v_val_917_ = lean_ctor_get(v_t_x3f_913_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_t_x3f_913_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_919_ = v_t_x3f_913_;
v_isShared_920_ = v_isSharedCheck_1029_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_val_917_);
lean_dec(v_t_x3f_913_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_1029_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0));
lean_inc_ref(v___x_909_);
lean_inc_ref(v___x_908_);
lean_inc_ref(v___x_907_);
v___x_922_ = l_Lean_Name_mkStr4(v___x_907_, v___x_908_, v___x_909_, v___x_921_);
lean_inc(v_val_917_);
v___x_923_ = l_Lean_Syntax_isOfKind(v_val_917_, v___x_922_);
lean_dec(v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
lean_del_object(v___x_919_);
lean_dec(v___x_900_);
v___x_924_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1));
lean_inc_ref(v___x_909_);
lean_inc_ref(v___x_908_);
lean_inc_ref(v___x_907_);
v___x_925_ = l_Lean_Name_mkStr4(v___x_907_, v___x_908_, v___x_909_, v___x_924_);
lean_inc(v_val_917_);
v___x_926_ = l_Lean_Syntax_isOfKind(v_val_917_, v___x_925_);
lean_dec(v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_927_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_909_);
lean_inc_ref(v___x_908_);
lean_inc_ref(v___x_907_);
v___x_928_ = l_Lean_Name_mkStr4(v___x_907_, v___x_908_, v___x_909_, v___x_927_);
lean_inc(v_val_917_);
v___x_929_ = l_Lean_Syntax_isOfKind(v_val_917_, v___x_928_);
lean_dec(v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_930_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_909_);
lean_inc_ref(v___x_908_);
lean_inc_ref(v___x_907_);
v___x_931_ = l_Lean_Name_mkStr4(v___x_907_, v___x_908_, v___x_909_, v___x_930_);
lean_inc(v_val_917_);
v___x_932_ = l_Lean_Syntax_isOfKind(v_val_917_, v___x_931_);
lean_dec(v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_933_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_934_ = l_Lean_Name_mkStr4(v___x_907_, v___x_908_, v___x_909_, v___x_933_);
lean_inc(v_val_917_);
v___x_935_ = l_Lean_Syntax_isOfKind(v_val_917_, v___x_934_);
lean_dec(v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___f_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec(v___x_912_);
lean_dec(v_toPure_902_);
v___f_936_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_936_, 0, v___f_916_);
v___x_937_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_938_ = l_Lean_throwErrorAt___redArg(v_inst_910_, v_inst_911_, v_val_917_, v___x_937_);
v___x_939_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_938_, v___f_936_);
return v___x_939_;
}
else
{
lean_object* v___f_940_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___f_940_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_940_, 0, v___f_916_);
v___x_945_ = l_Lean_Syntax_getArg(v_val_917_, v___x_912_);
lean_dec(v___x_912_);
v___x_946_ = l_Lean_Syntax_isNone(v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = lean_unsigned_to_nat(2u);
v___x_948_ = l_Lean_Syntax_matchesNull(v___x_945_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec(v_toPure_902_);
v___x_949_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_950_ = l_Lean_throwErrorAt___redArg(v_inst_910_, v_inst_911_, v_val_917_, v___x_949_);
v___x_951_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_950_, v___f_940_);
return v___x_951_;
}
else
{
lean_dec(v_val_917_);
lean_dec_ref(v_inst_911_);
lean_dec_ref(v_inst_910_);
goto v___jp_941_;
}
}
else
{
lean_dec(v___x_945_);
lean_dec(v_val_917_);
lean_dec_ref(v_inst_911_);
lean_dec_ref(v_inst_910_);
goto v___jp_941_;
}
v___jp_941_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = lean_box(0);
v___x_943_ = lean_apply_2(v_toPure_902_, lean_box(0), v___x_942_);
v___x_944_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_943_, v___f_940_);
return v___x_944_;
}
}
}
else
{
lean_object* v___f_952_; lean_object* v___x_957_; uint8_t v___x_958_; 
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_952_, 0, v___f_916_);
v___x_957_ = l_Lean_Syntax_getArg(v_val_917_, v___x_912_);
lean_dec(v___x_912_);
v___x_958_ = l_Lean_Syntax_isNone(v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_959_ = lean_unsigned_to_nat(2u);
v___x_960_ = l_Lean_Syntax_matchesNull(v___x_957_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec(v_toPure_902_);
v___x_961_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_962_ = l_Lean_throwErrorAt___redArg(v_inst_910_, v_inst_911_, v_val_917_, v___x_961_);
v___x_963_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_962_, v___f_952_);
return v___x_963_;
}
else
{
lean_dec(v_val_917_);
lean_dec_ref(v_inst_911_);
lean_dec_ref(v_inst_910_);
goto v___jp_953_;
}
}
else
{
lean_dec(v___x_957_);
lean_dec(v_val_917_);
lean_dec_ref(v_inst_911_);
lean_dec_ref(v_inst_910_);
goto v___jp_953_;
}
v___jp_953_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = lean_box(0);
v___x_955_ = lean_apply_2(v_toPure_902_, lean_box(0), v___x_954_);
v___x_956_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_955_, v___f_952_);
return v___x_956_;
}
}
}
else
{
lean_object* v___f_964_; lean_object* v___x_969_; uint8_t v___x_970_; 
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
v___f_964_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_964_, 0, v___f_916_);
v___x_969_ = l_Lean_Syntax_getArg(v_val_917_, v___x_912_);
lean_dec(v___x_912_);
v___x_970_ = l_Lean_Syntax_isNone(v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_971_ = lean_unsigned_to_nat(2u);
v___x_972_ = l_Lean_Syntax_matchesNull(v___x_969_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec(v_toPure_902_);
v___x_973_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_974_ = l_Lean_throwErrorAt___redArg(v_inst_910_, v_inst_911_, v_val_917_, v___x_973_);
v___x_975_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_974_, v___f_964_);
return v___x_975_;
}
else
{
lean_dec(v_val_917_);
lean_dec_ref(v_inst_911_);
lean_dec_ref(v_inst_910_);
goto v___jp_965_;
}
}
else
{
lean_dec(v___x_969_);
lean_dec(v_val_917_);
lean_dec_ref(v_inst_911_);
lean_dec_ref(v_inst_910_);
goto v___jp_965_;
}
v___jp_965_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = lean_box(0);
v___x_967_ = lean_apply_2(v_toPure_902_, lean_box(0), v___x_966_);
v___x_968_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_967_, v___f_964_);
return v___x_968_;
}
}
}
else
{
lean_object* v___f_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_dec(v_val_917_);
lean_dec(v___x_912_);
lean_dec_ref(v_inst_911_);
lean_dec_ref(v_inst_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
v___f_976_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_976_, 0, v___f_916_);
v___x_977_ = lean_box(0);
v___x_978_ = lean_apply_2(v_toPure_902_, lean_box(0), v___x_977_);
v___x_979_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_978_, v___f_976_);
return v___x_979_;
}
}
else
{
lean_object* v___f_980_; uint8_t v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; uint8_t v___y_985_; lean_object* v___y_993_; uint8_t v___y_994_; uint8_t v___y_995_; lean_object* v_s_1002_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
v___f_980_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_980_, 0, v___f_916_);
v___x_1020_ = l_Lean_Syntax_getArg(v_val_917_, v___x_912_);
v___x_1021_ = l_Lean_Syntax_isNone(v___x_1020_);
if (v___x_1021_ == 0)
{
uint8_t v___x_1022_; 
lean_inc(v___x_1020_);
v___x_1022_ = l_Lean_Syntax_matchesNull(v___x_1020_, v___x_912_);
lean_dec(v___x_912_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_dec(v___x_1020_);
lean_del_object(v___x_919_);
lean_dec(v_toPure_902_);
lean_dec(v___x_900_);
v___x_1023_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1024_ = l_Lean_throwErrorAt___redArg(v_inst_910_, v_inst_911_, v_val_917_, v___x_1023_);
v___x_1025_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_1024_, v___f_980_);
return v___x_1025_;
}
else
{
lean_object* v_s_1026_; lean_object* v___x_1027_; 
v_s_1026_ = l_Lean_Syntax_getArg(v___x_1020_, v___x_900_);
lean_dec(v___x_1020_);
v___x_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_s_1026_);
v_s_1002_ = v___x_1027_;
goto v___jp_1001_;
}
}
else
{
lean_object* v___x_1028_; 
lean_dec(v___x_1020_);
lean_dec(v___x_912_);
v___x_1028_ = lean_box(0);
v_s_1002_ = v___x_1028_;
goto v___jp_1001_;
}
v___jp_981_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_986_, 0, v_val_917_);
lean_ctor_set(v___x_986_, 1, v___y_984_);
lean_ctor_set(v___x_986_, 2, v___y_983_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*3, v___y_985_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*3 + 1, v___y_982_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_986_);
v___x_988_ = v___x_919_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_991_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_apply_2(v_toPure_902_, lean_box(0), v___x_988_);
v___x_990_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_989_, v___f_980_);
return v___x_990_;
}
}
v___jp_992_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_996_ = lean_mk_empty_array_with_capacity(v___x_900_);
lean_dec(v___x_900_);
v___x_997_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_997_, 0, v_val_917_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
lean_ctor_set(v___x_997_, 2, v___y_993_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*3, v___y_995_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*3 + 1, v___y_994_);
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
v___x_999_ = lean_apply_2(v_toPure_902_, lean_box(0), v___x_998_);
v___x_1000_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_999_, v___f_980_);
return v___x_1000_;
}
v___jp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = lean_unsigned_to_nat(2u);
v___x_1004_ = l_Lean_Syntax_getArg(v_val_917_, v___x_1003_);
lean_inc(v___x_1004_);
v___x_1005_ = l_Lean_Syntax_matchesNull(v___x_1004_, v___x_1003_);
if (v___x_1005_ == 0)
{
uint8_t v___x_1006_; 
lean_del_object(v___x_919_);
v___x_1006_ = l_Lean_Syntax_matchesNull(v___x_1004_, v___x_900_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec(v_s_1002_);
lean_dec(v_toPure_902_);
lean_dec(v___x_900_);
v___x_1007_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1008_ = l_Lean_throwErrorAt___redArg(v_inst_910_, v_inst_911_, v_val_917_, v___x_1007_);
v___x_1009_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_1008_, v___f_980_);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; lean_object* v_body_1011_; 
lean_dec_ref(v_inst_911_);
lean_dec_ref(v_inst_910_);
v___x_1010_ = lean_unsigned_to_nat(3u);
v_body_1011_ = l_Lean_Syntax_getArg(v_val_917_, v___x_1010_);
if (lean_obj_tag(v_s_1002_) == 0)
{
v___y_993_ = v_body_1011_;
v___y_994_ = v___x_1005_;
v___y_995_ = v___x_1005_;
goto v___jp_992_;
}
else
{
lean_dec_ref_known(v_s_1002_, 1);
v___y_993_ = v_body_1011_;
v___y_994_ = v___x_1005_;
v___y_995_ = v___x_1006_;
goto v___jp_992_;
}
}
}
else
{
lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = l_Lean_Syntax_getArg(v___x_1004_, v___x_900_);
lean_dec(v___x_1004_);
lean_inc(v___x_1012_);
v___x_1013_ = l_Lean_Syntax_matchesNull(v___x_1012_, v___x_900_);
lean_dec(v___x_900_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v_body_1015_; lean_object* v_vars_1016_; 
lean_dec_ref(v_inst_911_);
lean_dec_ref(v_inst_910_);
v___x_1014_ = lean_unsigned_to_nat(3u);
v_body_1015_ = l_Lean_Syntax_getArg(v_val_917_, v___x_1014_);
v_vars_1016_ = l_Lean_Syntax_getArgs(v___x_1012_);
lean_dec(v___x_1012_);
if (lean_obj_tag(v_s_1002_) == 0)
{
v___y_982_ = v___x_1013_;
v___y_983_ = v_body_1015_;
v___y_984_ = v_vars_1016_;
v___y_985_ = v___x_1013_;
goto v___jp_981_;
}
else
{
lean_dec_ref_known(v_s_1002_, 1);
v___y_982_ = v___x_1013_;
v___y_983_ = v_body_1015_;
v___y_984_ = v_vars_1016_;
v___y_985_ = v___x_1005_;
goto v___jp_981_;
}
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec(v___x_1012_);
lean_dec(v_s_1002_);
lean_del_object(v___x_919_);
lean_dec(v_toPure_902_);
v___x_1017_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
v___x_1018_ = l_Lean_throwErrorAt___redArg(v_inst_910_, v_inst_911_, v_val_917_, v___x_1017_);
v___x_1019_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_1018_, v___f_980_);
return v___x_1019_;
}
}
}
}
}
}
else
{
lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec(v_t_x3f_913_);
lean_dec(v___x_912_);
lean_dec_ref(v_inst_911_);
lean_dec_ref(v_inst_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
lean_dec(v___x_900_);
v___f_1030_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1030_, 0, v___f_916_);
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_apply_2(v_toPure_902_, lean_box(0), v___x_1031_);
v___x_1033_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_1032_, v___f_1030_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed(lean_object* v_stx_1034_, lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v_toPure_1037_, lean_object* v_d_x3f_1038_, lean_object* v_toBind_1039_, lean_object* v_toFunctor_1040_, lean_object* v___f_1041_, lean_object* v___x_1042_, lean_object* v___x_1043_, lean_object* v___x_1044_, lean_object* v_inst_1045_, lean_object* v_inst_1046_, lean_object* v___x_1047_, lean_object* v_t_x3f_1048_, lean_object* v_terminationBy_x3f_x3f_1049_){
_start:
{
uint8_t v___x_3232__boxed_1050_; lean_object* v_res_1051_; 
v___x_3232__boxed_1050_ = lean_unbox(v___x_1036_);
v_res_1051_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19(v_stx_1034_, v___x_1035_, v___x_3232__boxed_1050_, v_toPure_1037_, v_d_x3f_1038_, v_toBind_1039_, v_toFunctor_1040_, v___f_1041_, v___x_1042_, v___x_1043_, v___x_1044_, v_inst_1045_, v_inst_1046_, v___x_1047_, v_t_x3f_1048_, v_terminationBy_x3f_x3f_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* v___f_1052_, lean_object* v_terminationBy_x3f_x3f_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_apply_1(v___f_1052_, v_terminationBy_x3f_x3f_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_stx_1079_){
_start:
{
if (lean_obj_tag(v_stx_1079_) == 0)
{
lean_object* v_toApplicative_1080_; lean_object* v_toPure_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_toApplicative_1080_ = lean_ctor_get(v_inst_1077_, 0);
lean_inc_ref(v_toApplicative_1080_);
lean_dec_ref(v_inst_1078_);
lean_dec_ref(v_inst_1077_);
v_toPure_1081_ = lean_ctor_get(v_toApplicative_1080_, 1);
lean_inc(v_toPure_1081_);
lean_dec_ref(v_toApplicative_1080_);
v___x_1082_ = 1;
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1085_, 0, v_stx_1079_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
lean_ctor_set(v___x_1085_, 2, v___x_1084_);
lean_ctor_set(v___x_1085_, 3, v___x_1084_);
lean_ctor_set(v___x_1085_, 4, v___x_1084_);
lean_ctor_set(v___x_1085_, 5, v___x_1083_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*6, v___x_1082_);
v___x_1086_ = lean_apply_2(v_toPure_1081_, lean_box(0), v___x_1085_);
return v___x_1086_;
}
else
{
lean_object* v_toApplicative_1087_; lean_object* v_toBind_1088_; lean_object* v_toFunctor_1089_; lean_object* v_toPure_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_toApplicative_1087_ = lean_ctor_get(v_inst_1077_, 0);
v_toBind_1088_ = lean_ctor_get(v_inst_1077_, 1);
v_toFunctor_1089_ = lean_ctor_get(v_toApplicative_1087_, 0);
v_toPure_1090_ = lean_ctor_get(v_toApplicative_1087_, 1);
v___x_1091_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__0));
v___x_1092_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__1));
v___x_1093_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__2));
v___x_1094_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__4));
lean_inc(v_stx_1079_);
v___x_1095_ = l_Lean_Syntax_isOfKind(v_stx_1079_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1096_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1097_ = lean_box(0);
lean_inc_n(v_stx_1079_, 2);
v___x_1098_ = l_Lean_Syntax_formatStx(v_stx_1079_, v___x_1097_, v___x_1095_);
v___x_1099_ = l_Std_Format_defWidth;
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = l_Std_Format_pretty(v___x_1098_, v___x_1099_, v___x_1100_, v___x_1100_);
v___x_1102_ = lean_string_append(v___x_1096_, v___x_1101_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1104_ = lean_string_append(v___x_1102_, v___x_1103_);
v___x_1105_ = l_Lean_Syntax_getKind(v_stx_1079_);
v___x_1106_ = 1;
v___x_1107_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1105_, v___x_1106_);
v___x_1108_ = lean_string_append(v___x_1104_, v___x_1107_);
lean_dec_ref(v___x_1107_);
v___x_1109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
v___x_1110_ = l_Lean_MessageData_ofFormat(v___x_1109_);
v___x_1111_ = l_Lean_throwErrorAt___redArg(v_inst_1077_, v_inst_1078_, v_stx_1079_, v___x_1110_);
return v___x_1111_;
}
else
{
lean_object* v___f_1112_; lean_object* v___x_1113_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v_d_x3f_1118_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v_t_x3f_1149_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___f_1112_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__7));
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1186_ = l_Lean_Syntax_getArg(v_stx_1079_, v___x_1113_);
v___x_1187_ = l_Lean_Syntax_isNone(v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1186_);
v___x_1189_ = l_Lean_Syntax_matchesNull(v___x_1186_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_dec(v___x_1186_);
v___x_1190_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1191_ = lean_box(0);
lean_inc_n(v_stx_1079_, 2);
v___x_1192_ = l_Lean_Syntax_formatStx(v_stx_1079_, v___x_1191_, v___x_1189_);
v___x_1193_ = l_Std_Format_defWidth;
v___x_1194_ = l_Std_Format_pretty(v___x_1192_, v___x_1193_, v___x_1113_, v___x_1113_);
v___x_1195_ = lean_string_append(v___x_1190_, v___x_1194_);
lean_dec_ref(v___x_1194_);
v___x_1196_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1197_ = lean_string_append(v___x_1195_, v___x_1196_);
v___x_1198_ = l_Lean_Syntax_getKind(v_stx_1079_);
v___x_1199_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1198_, v___x_1095_);
v___x_1200_ = lean_string_append(v___x_1197_, v___x_1199_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
v___x_1202_ = l_Lean_MessageData_ofFormat(v___x_1201_);
v___x_1203_ = l_Lean_throwErrorAt___redArg(v_inst_1077_, v_inst_1078_, v_stx_1079_, v___x_1202_);
return v___x_1203_;
}
else
{
lean_object* v_t_x3f_1204_; lean_object* v___x_1205_; 
v_t_x3f_1204_ = l_Lean_Syntax_getArg(v___x_1186_, v___x_1113_);
lean_dec(v___x_1186_);
v___x_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_t_x3f_1204_);
v_t_x3f_1149_ = v___x_1205_;
goto v___jp_1148_;
}
}
else
{
lean_object* v___x_1206_; 
lean_dec(v___x_1186_);
v___x_1206_ = lean_box(0);
v_t_x3f_1149_ = v___x_1206_;
goto v___jp_1148_;
}
v___jp_1114_:
{
lean_object* v___x_1119_; lean_object* v___f_1120_; 
v___x_1119_ = lean_box(v___x_1095_);
lean_inc(v_toBind_1088_);
lean_inc(v_toPure_1090_);
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed), 16, 15);
lean_closure_set(v___f_1120_, 0, v_stx_1079_);
lean_closure_set(v___f_1120_, 1, v___x_1113_);
lean_closure_set(v___f_1120_, 2, v___x_1119_);
lean_closure_set(v___f_1120_, 3, v_toPure_1090_);
lean_closure_set(v___f_1120_, 4, v_d_x3f_1118_);
lean_closure_set(v___f_1120_, 5, v_toBind_1088_);
lean_closure_set(v___f_1120_, 6, v_toFunctor_1089_);
lean_closure_set(v___f_1120_, 7, v___f_1112_);
lean_closure_set(v___f_1120_, 8, v___x_1091_);
lean_closure_set(v___f_1120_, 9, v___x_1092_);
lean_closure_set(v___f_1120_, 10, v___x_1093_);
lean_closure_set(v___f_1120_, 11, v_inst_1077_);
lean_closure_set(v___f_1120_, 12, v_inst_1078_);
lean_closure_set(v___f_1120_, 13, v___y_1116_);
lean_closure_set(v___f_1120_, 14, v___y_1115_);
if (lean_obj_tag(v___y_1117_) == 1)
{
lean_object* v_val_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1137_; 
v_val_1121_ = lean_ctor_get(v___y_1117_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___y_1117_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1123_ = v___y_1117_;
v_isShared_1124_ = v_isSharedCheck_1137_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_val_1121_);
lean_dec(v___y_1117_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1137_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__8));
lean_inc(v_val_1121_);
v___x_1126_ = l_Lean_Syntax_isOfKind(v_val_1121_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___f_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_del_object(v___x_1123_);
lean_dec(v_val_1121_);
v___f_1127_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1127_, 0, v___f_1120_);
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_apply_2(v_toPure_1090_, lean_box(0), v___x_1128_);
v___x_1130_ = lean_apply_4(v_toBind_1088_, lean_box(0), lean_box(0), v___x_1129_, v___f_1127_);
return v___x_1130_;
}
else
{
lean_object* v___f_1131_; lean_object* v___x_1133_; 
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1131_, 0, v___f_1120_);
if (v_isShared_1124_ == 0)
{
v___x_1133_ = v___x_1123_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_val_1121_);
v___x_1133_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_apply_2(v_toPure_1090_, lean_box(0), v___x_1133_);
v___x_1135_ = lean_apply_4(v_toBind_1088_, lean_box(0), lean_box(0), v___x_1134_, v___f_1131_);
return v___x_1135_;
}
}
}
}
else
{
lean_object* v___f_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec(v___y_1117_);
v___f_1138_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1138_, 0, v___f_1120_);
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_apply_2(v_toPure_1090_, lean_box(0), v___x_1139_);
v___x_1141_ = lean_apply_4(v_toBind_1088_, lean_box(0), lean_box(0), v___x_1140_, v___f_1138_);
return v___x_1141_;
}
}
v___jp_1142_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___y_1146_);
v___y_1115_ = v___y_1143_;
v___y_1116_ = v___y_1144_;
v___y_1117_ = v___y_1145_;
v_d_x3f_1118_ = v___x_1147_;
goto v___jp_1114_;
}
v___jp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = l_Lean_Syntax_getArg(v_stx_1079_, v___x_1150_);
v___x_1152_ = l_Lean_Syntax_isNone(v___x_1151_);
if (v___x_1152_ == 0)
{
uint8_t v___x_1153_; 
lean_inc(v___x_1151_);
v___x_1153_ = l_Lean_Syntax_matchesNull(v___x_1151_, v___x_1150_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec(v___x_1151_);
lean_dec(v_t_x3f_1149_);
v___x_1154_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1155_ = lean_box(0);
lean_inc_n(v_stx_1079_, 2);
v___x_1156_ = l_Lean_Syntax_formatStx(v_stx_1079_, v___x_1155_, v___x_1153_);
v___x_1157_ = l_Std_Format_defWidth;
v___x_1158_ = l_Std_Format_pretty(v___x_1156_, v___x_1157_, v___x_1113_, v___x_1113_);
v___x_1159_ = lean_string_append(v___x_1154_, v___x_1158_);
lean_dec_ref(v___x_1158_);
v___x_1160_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1161_ = lean_string_append(v___x_1159_, v___x_1160_);
v___x_1162_ = l_Lean_Syntax_getKind(v_stx_1079_);
v___x_1163_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1162_, v___x_1095_);
v___x_1164_ = lean_string_append(v___x_1161_, v___x_1163_);
lean_dec_ref(v___x_1163_);
v___x_1165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
v___x_1166_ = l_Lean_MessageData_ofFormat(v___x_1165_);
v___x_1167_ = l_Lean_throwErrorAt___redArg(v_inst_1077_, v_inst_1078_, v_stx_1079_, v___x_1166_);
return v___x_1167_;
}
else
{
lean_object* v_d_x3f_1168_; 
v_d_x3f_1168_ = l_Lean_Syntax_getArg(v___x_1151_, v___x_1113_);
lean_dec(v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__9));
lean_inc(v_d_x3f_1168_);
v___x_1170_ = l_Lean_Syntax_isOfKind(v_d_x3f_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec(v_d_x3f_1168_);
lean_dec(v_t_x3f_1149_);
v___x_1171_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1172_ = lean_box(0);
lean_inc_n(v_stx_1079_, 2);
v___x_1173_ = l_Lean_Syntax_formatStx(v_stx_1079_, v___x_1172_, v___x_1152_);
v___x_1174_ = l_Std_Format_defWidth;
v___x_1175_ = l_Std_Format_pretty(v___x_1173_, v___x_1174_, v___x_1113_, v___x_1113_);
v___x_1176_ = lean_string_append(v___x_1171_, v___x_1175_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1178_ = lean_string_append(v___x_1176_, v___x_1177_);
v___x_1179_ = l_Lean_Syntax_getKind(v_stx_1079_);
v___x_1180_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1179_, v___x_1153_);
v___x_1181_ = lean_string_append(v___x_1178_, v___x_1180_);
lean_dec_ref(v___x_1180_);
v___x_1182_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
v___x_1183_ = l_Lean_MessageData_ofFormat(v___x_1182_);
v___x_1184_ = l_Lean_throwErrorAt___redArg(v_inst_1077_, v_inst_1078_, v_stx_1079_, v___x_1183_);
return v___x_1184_;
}
else
{
lean_inc(v_toPure_1090_);
lean_inc_ref(v_toFunctor_1089_);
lean_inc(v_toBind_1088_);
lean_inc(v_t_x3f_1149_);
v___y_1143_ = v_t_x3f_1149_;
v___y_1144_ = v___x_1150_;
v___y_1145_ = v_t_x3f_1149_;
v___y_1146_ = v_d_x3f_1168_;
goto v___jp_1142_;
}
}
else
{
lean_inc(v_toPure_1090_);
lean_inc_ref(v_toFunctor_1089_);
lean_inc(v_toBind_1088_);
lean_inc(v_t_x3f_1149_);
v___y_1143_ = v_t_x3f_1149_;
v___y_1144_ = v___x_1150_;
v___y_1145_ = v_t_x3f_1149_;
v___y_1146_ = v_d_x3f_1168_;
goto v___jp_1142_;
}
}
}
else
{
lean_object* v___x_1185_; 
lean_inc(v_toPure_1090_);
lean_inc_ref(v_toFunctor_1089_);
lean_inc(v_toBind_1088_);
lean_dec(v___x_1151_);
v___x_1185_ = lean_box(0);
lean_inc(v_t_x3f_1149_);
v___y_1115_ = v_t_x3f_1149_;
v___y_1116_ = v___x_1150_;
v___y_1117_ = v_t_x3f_1149_;
v_d_x3f_1118_ = v___x_1185_;
goto v___jp_1114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* v_m_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_stx_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_Elab_elabTerminationHints___redArg(v_inst_1208_, v_inst_1209_, v_stx_1210_);
return v___x_1211_;
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
