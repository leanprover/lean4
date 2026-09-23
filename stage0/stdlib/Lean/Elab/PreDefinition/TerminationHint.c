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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_118_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
uint8_t v_suppressElabErrors_boxed_194_; uint8_t v___y_3395__boxed_195_; uint8_t v_res_196_; lean_object* v_r_197_; 
v_suppressElabErrors_boxed_194_ = lean_unbox(v_suppressElabErrors_191_);
v___y_3395__boxed_195_ = lean_unbox(v___y_192_);
v_res_196_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_194_, v___y_3395__boxed_195_, v_x_193_);
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
uint8_t v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; uint8_t v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v_currNamespace_228_; lean_object* v_openDecls_229_; lean_object* v___y_230_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; uint8_t v___y_261_; uint8_t v___y_262_; lean_object* v___y_263_; uint8_t v___y_264_; lean_object* v___y_265_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; uint8_t v___y_288_; uint8_t v___y_289_; lean_object* v___y_290_; uint8_t v___y_291_; lean_object* v___y_292_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; uint8_t v___y_300_; uint8_t v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; uint8_t v___y_304_; uint8_t v___x_309_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; uint8_t v___y_316_; uint8_t v___y_317_; lean_object* v___y_318_; uint8_t v___y_319_; uint8_t v___y_321_; uint8_t v___x_339_; 
v___x_309_ = 2;
v___x_339_ = l_Lean_instBEqMessageSeverity_beq(v_severity_215_, v___x_309_);
if (v___x_339_ == 0)
{
v___y_321_ = v___x_339_;
goto v___jp_320_;
}
else
{
uint8_t v___x_340_; 
lean_inc_ref(v_msgData_214_);
v___x_340_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_214_);
v___y_321_ = v___x_340_;
goto v___jp_320_;
}
v___jp_220_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_env_235_; lean_object* v_nextMacroScope_236_; lean_object* v_ngen_237_; lean_object* v_auxDeclNGen_238_; lean_object* v_traceState_239_; lean_object* v_cache_240_; lean_object* v_messages_241_; lean_object* v_infoState_242_; lean_object* v_snapshotTasks_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_254_; 
lean_inc(v_openDecls_229_);
lean_inc(v_currNamespace_228_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_currNamespace_228_);
lean_ctor_set(v___x_231_, 1, v_openDecls_229_);
v___x_232_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___y_226_);
lean_inc_ref(v___y_227_);
lean_inc_ref(v___y_224_);
v___x_233_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_233_, 0, v___y_224_);
lean_ctor_set(v___x_233_, 1, v___y_223_);
lean_ctor_set(v___x_233_, 2, v___y_222_);
lean_ctor_set(v___x_233_, 3, v___y_227_);
lean_ctor_set(v___x_233_, 4, v___x_232_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*5, v___y_221_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*5 + 1, v___y_225_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*5 + 2, v_isSilent_216_);
v___x_234_ = lean_st_ref_take(v___y_230_);
v_env_235_ = lean_ctor_get(v___x_234_, 0);
v_nextMacroScope_236_ = lean_ctor_get(v___x_234_, 1);
v_ngen_237_ = lean_ctor_get(v___x_234_, 2);
v_auxDeclNGen_238_ = lean_ctor_get(v___x_234_, 3);
v_traceState_239_ = lean_ctor_get(v___x_234_, 4);
v_cache_240_ = lean_ctor_get(v___x_234_, 5);
v_messages_241_ = lean_ctor_get(v___x_234_, 6);
v_infoState_242_ = lean_ctor_get(v___x_234_, 7);
v_snapshotTasks_243_ = lean_ctor_get(v___x_234_, 8);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_254_ == 0)
{
v___x_245_ = v___x_234_;
v_isShared_246_ = v_isSharedCheck_254_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_snapshotTasks_243_);
lean_inc(v_infoState_242_);
lean_inc(v_messages_241_);
lean_inc(v_cache_240_);
lean_inc(v_traceState_239_);
lean_inc(v_auxDeclNGen_238_);
lean_inc(v_ngen_237_);
lean_inc(v_nextMacroScope_236_);
lean_inc(v_env_235_);
lean_dec(v___x_234_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_254_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = lean_box(0);
v___x_248_ = l_Lean_MessageLog_add(v___x_233_, v_messages_241_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 6, v___x_248_);
v___x_250_ = v___x_245_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_env_235_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_nextMacroScope_236_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_ngen_237_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_auxDeclNGen_238_);
lean_ctor_set(v_reuseFailAlloc_253_, 4, v_traceState_239_);
lean_ctor_set(v_reuseFailAlloc_253_, 5, v_cache_240_);
lean_ctor_set(v_reuseFailAlloc_253_, 6, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_253_, 7, v_infoState_242_);
lean_ctor_set(v_reuseFailAlloc_253_, 8, v_snapshotTasks_243_);
v___x_250_ = v_reuseFailAlloc_253_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_st_ref_put(v___y_230_, v___x_250_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_247_);
return v___x_252_;
}
}
}
v___jp_255_:
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
lean_inc_ref_n(v___y_260_, 2);
v___x_272_ = l_Lean_FileMap_toPosition(v___y_260_, v___y_259_);
lean_dec(v___y_259_);
v___x_273_ = l_Lean_FileMap_toPosition(v___y_260_, v___y_265_);
lean_dec(v___y_265_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
v___x_275_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0));
if (v___y_261_ == 0)
{
lean_del_object(v___x_270_);
lean_dec_ref(v___y_256_);
v___y_221_ = v___y_262_;
v___y_222_ = v___x_274_;
v___y_223_ = v___x_272_;
v___y_224_ = v___y_263_;
v___y_225_ = v___y_264_;
v___y_226_ = v_a_268_;
v___y_227_ = v___x_275_;
v_currNamespace_228_ = v___y_258_;
v_openDecls_229_ = v___y_257_;
v___y_230_ = v___y_218_;
goto v___jp_220_;
}
else
{
uint8_t v___x_276_; 
lean_inc(v_a_268_);
v___x_276_ = l_Lean_MessageData_hasTag(v___y_256_, v_a_268_);
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
v___y_221_ = v___y_262_;
v___y_222_ = v___x_274_;
v___y_223_ = v___x_272_;
v___y_224_ = v___y_263_;
v___y_225_ = v___y_264_;
v___y_226_ = v_a_268_;
v___y_227_ = v___x_275_;
v_currNamespace_228_ = v___y_258_;
v_openDecls_229_ = v___y_257_;
v___y_230_ = v___y_218_;
goto v___jp_220_;
}
}
}
}
v___jp_282_:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Syntax_getTailPos_x3f(v___y_286_, v___y_289_);
lean_dec(v___y_286_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_inc(v___y_292_);
v___y_256_ = v___y_283_;
v___y_257_ = v___y_284_;
v___y_258_ = v___y_285_;
v___y_259_ = v___y_292_;
v___y_260_ = v___y_287_;
v___y_261_ = v___y_288_;
v___y_262_ = v___y_289_;
v___y_263_ = v___y_290_;
v___y_264_ = v___y_291_;
v___y_265_ = v___y_292_;
goto v___jp_255_;
}
else
{
lean_object* v_val_294_; 
v_val_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_val_294_);
lean_dec_ref_known(v___x_293_, 1);
v___y_256_ = v___y_283_;
v___y_257_ = v___y_284_;
v___y_258_ = v___y_285_;
v___y_259_ = v___y_292_;
v___y_260_ = v___y_287_;
v___y_261_ = v___y_288_;
v___y_262_ = v___y_289_;
v___y_263_ = v___y_290_;
v___y_264_ = v___y_291_;
v___y_265_ = v_val_294_;
goto v___jp_255_;
}
}
v___jp_295_:
{
lean_object* v_ref_305_; lean_object* v___x_306_; 
v_ref_305_ = l_Lean_replaceRef(v_ref_213_, v___y_303_);
v___x_306_ = l_Lean_Syntax_getPos_x3f(v_ref_305_, v___y_301_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___y_283_ = v___y_296_;
v___y_284_ = v___y_297_;
v___y_285_ = v___y_298_;
v___y_286_ = v_ref_305_;
v___y_287_ = v___y_299_;
v___y_288_ = v___y_300_;
v___y_289_ = v___y_301_;
v___y_290_ = v___y_302_;
v___y_291_ = v___y_304_;
v___y_292_ = v___x_307_;
goto v___jp_282_;
}
else
{
lean_object* v_val_308_; 
v_val_308_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v___x_306_, 1);
v___y_283_ = v___y_296_;
v___y_284_ = v___y_297_;
v___y_285_ = v___y_298_;
v___y_286_ = v_ref_305_;
v___y_287_ = v___y_299_;
v___y_288_ = v___y_300_;
v___y_289_ = v___y_301_;
v___y_290_ = v___y_302_;
v___y_291_ = v___y_304_;
v___y_292_ = v_val_308_;
goto v___jp_282_;
}
}
v___jp_310_:
{
if (v___y_319_ == 0)
{
v___y_296_ = v___y_311_;
v___y_297_ = v___y_313_;
v___y_298_ = v___y_315_;
v___y_299_ = v___y_312_;
v___y_300_ = v___y_316_;
v___y_301_ = v___y_317_;
v___y_302_ = v___y_314_;
v___y_303_ = v___y_318_;
v___y_304_ = v_severity_215_;
goto v___jp_295_;
}
else
{
v___y_296_ = v___y_311_;
v___y_297_ = v___y_313_;
v___y_298_ = v___y_315_;
v___y_299_ = v___y_312_;
v___y_300_ = v___y_316_;
v___y_301_ = v___y_317_;
v___y_302_ = v___y_314_;
v___y_303_ = v___y_318_;
v___y_304_ = v___x_309_;
goto v___jp_295_;
}
}
v___jp_320_:
{
if (v___y_321_ == 0)
{
lean_object* v_toCold_322_; lean_object* v_ref_323_; uint8_t v_suppressElabErrors_324_; lean_object* v_fileName_325_; lean_object* v_fileMap_326_; lean_object* v_options_327_; lean_object* v_currNamespace_328_; lean_object* v_openDecls_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___f_332_; uint8_t v___x_333_; uint8_t v___x_334_; 
v_toCold_322_ = lean_ctor_get(v___y_217_, 0);
v_ref_323_ = lean_ctor_get(v___y_217_, 2);
v_suppressElabErrors_324_ = lean_ctor_get_uint8(v___y_217_, sizeof(void*)*3 + 1);
v_fileName_325_ = lean_ctor_get(v_toCold_322_, 0);
v_fileMap_326_ = lean_ctor_get(v_toCold_322_, 1);
v_options_327_ = lean_ctor_get(v_toCold_322_, 2);
v_currNamespace_328_ = lean_ctor_get(v_toCold_322_, 4);
v_openDecls_329_ = lean_ctor_get(v_toCold_322_, 5);
v___x_330_ = lean_box(v_suppressElabErrors_324_);
v___x_331_ = lean_box(v___y_321_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_332_, 0, v___x_330_);
lean_closure_set(v___f_332_, 1, v___x_331_);
v___x_333_ = 1;
v___x_334_ = l_Lean_instBEqMessageSeverity_beq(v_severity_215_, v___x_333_);
if (v___x_334_ == 0)
{
v___y_311_ = v___f_332_;
v___y_312_ = v_fileMap_326_;
v___y_313_ = v_openDecls_329_;
v___y_314_ = v_fileName_325_;
v___y_315_ = v_currNamespace_328_;
v___y_316_ = v_suppressElabErrors_324_;
v___y_317_ = v___y_321_;
v___y_318_ = v_ref_323_;
v___y_319_ = v___x_334_;
goto v___jp_310_;
}
else
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = l_Lean_warningAsError;
v___x_336_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_options_327_, v___x_335_);
v___y_311_ = v___f_332_;
v___y_312_ = v_fileMap_326_;
v___y_313_ = v_openDecls_329_;
v___y_314_ = v_fileName_325_;
v___y_315_ = v_currNamespace_328_;
v___y_316_ = v_suppressElabErrors_324_;
v___y_317_ = v___y_321_;
v___y_318_ = v_ref_323_;
v___y_319_ = v___x_336_;
goto v___jp_310_;
}
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v_msgData_214_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___boxed(lean_object* v_ref_341_, lean_object* v_msgData_342_, lean_object* v_severity_343_, lean_object* v_isSilent_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
uint8_t v_severity_boxed_348_; uint8_t v_isSilent_boxed_349_; lean_object* v_res_350_; 
v_severity_boxed_348_ = lean_unbox(v_severity_343_);
v_isSilent_boxed_349_ = lean_unbox(v_isSilent_344_);
v_res_350_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_341_, v_msgData_342_, v_severity_boxed_348_, v_isSilent_boxed_349_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v_ref_341_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(lean_object* v_ref_351_, lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
uint8_t v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; 
v___x_356_ = 1;
v___x_357_ = 0;
v___x_358_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_351_, v_msgData_352_, v___x_356_, v___x_357_, v___y_353_, v___y_354_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(lean_object* v_ref_359_, lean_object* v_msgData_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_359_, v_msgData_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v_ref_359_);
return v_res_364_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__0));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__2));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__4));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__6));
v___x_376_ = l_Lean_stringToMessageData(v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__8));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__10));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__12));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone(lean_object* v_hints_386_, lean_object* v_reason_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_ref_391_; lean_object* v_terminationBy_x3f_x3f_392_; lean_object* v_terminationBy_x3f_393_; lean_object* v_partialFixpoint_x3f_394_; lean_object* v_decreasingBy_x3f_395_; uint8_t v_warnIfRedundant_396_; lean_object* v___y_398_; lean_object* v___y_399_; 
v_ref_391_ = lean_ctor_get(v_hints_386_, 0);
lean_inc(v_ref_391_);
v_terminationBy_x3f_x3f_392_ = lean_ctor_get(v_hints_386_, 1);
lean_inc(v_terminationBy_x3f_x3f_392_);
v_terminationBy_x3f_393_ = lean_ctor_get(v_hints_386_, 2);
lean_inc(v_terminationBy_x3f_393_);
v_partialFixpoint_x3f_394_ = lean_ctor_get(v_hints_386_, 3);
lean_inc(v_partialFixpoint_x3f_394_);
v_decreasingBy_x3f_395_ = lean_ctor_get(v_hints_386_, 4);
lean_inc(v_decreasingBy_x3f_395_);
v_warnIfRedundant_396_ = lean_ctor_get_uint8(v_hints_386_, sizeof(void*)*6);
lean_dec_ref(v_hints_386_);
if (v_warnIfRedundant_396_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_decreasingBy_x3f_395_);
lean_dec(v_partialFixpoint_x3f_394_);
lean_dec(v_terminationBy_x3f_393_);
lean_dec(v_terminationBy_x3f_x3f_392_);
lean_dec(v_ref_391_);
lean_dec_ref(v_reason_387_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_x3f_392_) == 0)
{
if (lean_obj_tag(v_terminationBy_x3f_393_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_395_) == 0)
{
lean_dec(v_ref_391_);
if (lean_obj_tag(v_partialFixpoint_x3f_394_) == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v_reason_387_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
else
{
lean_object* v_val_408_; uint8_t v_fixpointType_409_; 
v_val_408_ = lean_ctor_get(v_partialFixpoint_x3f_394_, 0);
lean_inc(v_val_408_);
lean_dec_ref_known(v_partialFixpoint_x3f_394_, 1);
v_fixpointType_409_ = lean_ctor_get_uint8(v_val_408_, sizeof(void*)*2);
switch(v_fixpointType_409_)
{
case 0:
{
lean_object* v_ref_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_ref_410_ = lean_ctor_get(v_val_408_, 0);
lean_inc(v_ref_410_);
lean_dec(v_val_408_);
v___x_411_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__3, &l_Lean_Elab_TerminationHints_ensureNone___closed__3_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3);
v___x_412_ = l_Lean_stringToMessageData(v_reason_387_);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_410_, v___x_413_, v_a_388_, v_a_389_);
lean_dec(v_ref_410_);
return v___x_414_;
}
case 1:
{
lean_object* v_ref_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_ref_415_ = lean_ctor_get(v_val_408_, 0);
lean_inc(v_ref_415_);
lean_dec(v_val_408_);
v___x_416_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__5, &l_Lean_Elab_TerminationHints_ensureNone___closed__5_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5);
v___x_417_ = l_Lean_stringToMessageData(v_reason_387_);
v___x_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_415_, v___x_418_, v_a_388_, v_a_389_);
lean_dec(v_ref_415_);
return v___x_419_;
}
default: 
{
lean_object* v_ref_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_ref_420_ = lean_ctor_get(v_val_408_, 0);
lean_inc(v_ref_420_);
lean_dec(v_val_408_);
v___x_421_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__7, &l_Lean_Elab_TerminationHints_ensureNone___closed__7_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7);
v___x_422_ = l_Lean_stringToMessageData(v_reason_387_);
v___x_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_420_, v___x_423_, v_a_388_, v_a_389_);
lean_dec(v_ref_420_);
return v___x_424_;
}
}
}
}
else
{
if (lean_obj_tag(v_partialFixpoint_x3f_394_) == 0)
{
lean_object* v_val_425_; lean_object* v_ref_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_ref_391_);
v_val_425_ = lean_ctor_get(v_decreasingBy_x3f_395_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v_decreasingBy_x3f_395_, 1);
v_ref_426_ = lean_ctor_get(v_val_425_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_val_425_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v_val_425_, 1);
lean_dec(v_unused_437_);
v___x_428_ = v_val_425_;
v_isShared_429_ = v_isSharedCheck_436_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_ref_426_);
lean_dec(v_val_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_436_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_430_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__9, &l_Lean_Elab_TerminationHints_ensureNone___closed__9_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9);
v___x_431_ = l_Lean_stringToMessageData(v_reason_387_);
if (v_isShared_429_ == 0)
{
lean_ctor_set_tag(v___x_428_, 7);
lean_ctor_set(v___x_428_, 1, v___x_431_);
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_433_ = v___x_428_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_431_);
v___x_433_ = v_reuseFailAlloc_435_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_426_, v___x_433_, v_a_388_, v_a_389_);
lean_dec(v_ref_426_);
return v___x_434_;
}
}
}
else
{
lean_dec_ref_known(v_decreasingBy_x3f_395_, 1);
lean_dec(v_partialFixpoint_x3f_394_);
v___y_398_ = v_a_388_;
v___y_399_ = v_a_389_;
goto v___jp_397_;
}
}
}
else
{
if (lean_obj_tag(v_decreasingBy_x3f_395_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_394_) == 0)
{
lean_object* v_val_438_; lean_object* v_ref_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v_ref_391_);
v_val_438_ = lean_ctor_get(v_terminationBy_x3f_393_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v_terminationBy_x3f_393_, 1);
v_ref_439_ = lean_ctor_get(v_val_438_, 0);
lean_inc(v_ref_439_);
lean_dec(v_val_438_);
v___x_440_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__11, &l_Lean_Elab_TerminationHints_ensureNone___closed__11_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11);
v___x_441_ = l_Lean_stringToMessageData(v_reason_387_);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_439_, v___x_442_, v_a_388_, v_a_389_);
lean_dec(v_ref_439_);
return v___x_443_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_393_, 1);
lean_dec(v_partialFixpoint_x3f_394_);
v___y_398_ = v_a_388_;
v___y_399_ = v_a_389_;
goto v___jp_397_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_393_, 1);
lean_dec(v_decreasingBy_x3f_395_);
lean_dec(v_partialFixpoint_x3f_394_);
v___y_398_ = v_a_388_;
v___y_399_ = v_a_389_;
goto v___jp_397_;
}
}
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_393_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_395_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_394_) == 0)
{
lean_object* v_val_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v_ref_391_);
v_val_444_ = lean_ctor_get(v_terminationBy_x3f_x3f_392_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_392_, 1);
v___x_445_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__13, &l_Lean_Elab_TerminationHints_ensureNone___closed__13_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13);
v___x_446_ = l_Lean_stringToMessageData(v_reason_387_);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_val_444_, v___x_447_, v_a_388_, v_a_389_);
lean_dec(v_val_444_);
return v___x_448_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_392_, 1);
lean_dec(v_partialFixpoint_x3f_394_);
v___y_398_ = v_a_388_;
v___y_399_ = v_a_389_;
goto v___jp_397_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_392_, 1);
lean_dec(v_decreasingBy_x3f_395_);
lean_dec(v_partialFixpoint_x3f_394_);
v___y_398_ = v_a_388_;
v___y_399_ = v_a_389_;
goto v___jp_397_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_392_, 1);
lean_dec(v_decreasingBy_x3f_395_);
lean_dec(v_partialFixpoint_x3f_394_);
lean_dec(v_terminationBy_x3f_393_);
v___y_398_ = v_a_388_;
v___y_399_ = v_a_389_;
goto v___jp_397_;
}
}
}
v___jp_397_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_400_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__1, &l_Lean_Elab_TerminationHints_ensureNone___closed__1_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1);
v___x_401_ = l_Lean_stringToMessageData(v_reason_387_);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_391_, v___x_402_, v___y_398_, v___y_399_);
lean_dec(v_ref_391_);
return v___x_403_;
}
}
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
LEAN_EXPORT uint8_t l_Lean_Elab_TerminationHints_isNotNone(lean_object* v_hints_455_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_isNotNone___boxed(lean_object* v_hints_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Lean_Elab_TerminationHints_isNotNone(v_hints_465_);
lean_dec_ref(v_hints_465_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object* v_headerParams_468_, lean_object* v_hints_469_, lean_object* v_value_470_){
_start:
{
lean_object* v_ref_471_; lean_object* v_terminationBy_x3f_x3f_472_; lean_object* v_terminationBy_x3f_473_; lean_object* v_partialFixpoint_x3f_474_; lean_object* v_decreasingBy_x3f_475_; uint8_t v_warnIfRedundant_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_485_; 
v_ref_471_ = lean_ctor_get(v_hints_469_, 0);
v_terminationBy_x3f_x3f_472_ = lean_ctor_get(v_hints_469_, 1);
v_terminationBy_x3f_473_ = lean_ctor_get(v_hints_469_, 2);
v_partialFixpoint_x3f_474_ = lean_ctor_get(v_hints_469_, 3);
v_decreasingBy_x3f_475_ = lean_ctor_get(v_hints_469_, 4);
v_warnIfRedundant_476_ = lean_ctor_get_uint8(v_hints_469_, sizeof(void*)*6);
v_isSharedCheck_485_ = !lean_is_exclusive(v_hints_469_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v_hints_469_, 5);
lean_dec(v_unused_486_);
v___x_478_ = v_hints_469_;
v_isShared_479_ = v_isSharedCheck_485_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_decreasingBy_x3f_475_);
lean_inc(v_partialFixpoint_x3f_474_);
lean_inc(v_terminationBy_x3f_473_);
lean_inc(v_terminationBy_x3f_x3f_472_);
lean_inc(v_ref_471_);
lean_dec(v_hints_469_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_485_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_480_ = l_Lean_Expr_getNumHeadLambdas(v_value_470_);
v___x_481_ = lean_nat_sub(v___x_480_, v_headerParams_468_);
lean_dec(v___x_480_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 5, v___x_481_);
v___x_483_ = v___x_478_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_ref_471_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_terminationBy_x3f_x3f_472_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_terminationBy_x3f_473_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_partialFixpoint_x3f_474_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_decreasingBy_x3f_475_);
lean_ctor_set(v_reuseFailAlloc_484_, 5, v___x_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*6, v_warnIfRedundant_476_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(lean_object* v_headerParams_487_, lean_object* v_hints_488_, lean_object* v_value_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v_headerParams_487_, v_hints_488_, v_value_489_);
lean_dec_ref(v_value_489_);
lean_dec(v_headerParams_487_);
return v_res_490_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3));
v___x_498_ = l_Lean_MessageData_ofFormat(v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(lean_object* v_a_499_){
_start:
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_dec_eq(v_a_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_502_ = l_Nat_reprFast(v_a_499_);
v___x_503_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
v___x_504_ = l_Lean_MessageData_ofFormat(v___x_503_);
v___x_505_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; 
lean_dec(v_a_499_);
v___x_507_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(lean_object* v_msgData_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; lean_object* v_env_515_; lean_object* v___x_516_; lean_object* v_toCold_517_; lean_object* v_mctx_518_; lean_object* v_lctx_519_; lean_object* v_options_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_514_ = lean_st_ref_get(v___y_512_);
v_env_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_env_515_);
lean_dec(v___x_514_);
v___x_516_ = lean_st_ref_get(v___y_510_);
v_toCold_517_ = lean_ctor_get(v___y_511_, 0);
v_mctx_518_ = lean_ctor_get(v___x_516_, 0);
lean_inc_ref(v_mctx_518_);
lean_dec(v___x_516_);
v_lctx_519_ = lean_ctor_get(v___y_509_, 2);
v_options_520_ = lean_ctor_get(v_toCold_517_, 2);
lean_inc_ref(v_options_520_);
lean_inc_ref(v_lctx_519_);
v___x_521_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_521_, 0, v_env_515_);
lean_ctor_set(v___x_521_, 1, v_mctx_518_);
lean_ctor_set(v___x_521_, 2, v_lctx_519_);
lean_ctor_set(v___x_521_, 3, v_options_520_);
v___x_522_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_msgData_508_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(lean_object* v_msg_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_ref_537_; lean_object* v___x_538_; lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_547_; 
v_ref_537_ = lean_ctor_get(v___y_534_, 2);
v___x_538_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msg_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_547_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
lean_inc(v_ref_537_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v_ref_537_);
lean_ctor_set(v___x_543_, 1, v_a_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 1);
lean_ctor_set(v___x_541_, 0, v___x_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object* v_ref_555_, lean_object* v_msg_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_toCold_562_; lean_object* v_currRecDepth_563_; lean_object* v_ref_564_; uint8_t v_diag_565_; uint8_t v_suppressElabErrors_566_; lean_object* v_ref_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_toCold_562_ = lean_ctor_get(v___y_559_, 0);
v_currRecDepth_563_ = lean_ctor_get(v___y_559_, 1);
v_ref_564_ = lean_ctor_get(v___y_559_, 2);
v_diag_565_ = lean_ctor_get_uint8(v___y_559_, sizeof(void*)*3);
v_suppressElabErrors_566_ = lean_ctor_get_uint8(v___y_559_, sizeof(void*)*3 + 1);
v_ref_567_ = l_Lean_replaceRef(v_ref_555_, v_ref_564_);
lean_inc(v_currRecDepth_563_);
lean_inc_ref(v_toCold_562_);
v___x_568_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_568_, 0, v_toCold_562_);
lean_ctor_set(v___x_568_, 1, v_currRecDepth_563_);
lean_ctor_set(v___x_568_, 2, v_ref_567_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*3, v_diag_565_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*3 + 1, v_suppressElabErrors_566_);
v___x_569_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_556_, v___y_557_, v___y_558_, v___x_568_, v___y_560_);
lean_dec_ref_known(v___x_568_, 3);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object* v_ref_570_, lean_object* v_msg_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_570_, v_msg_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v_ref_570_);
return v_res_577_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__1(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__0));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__3(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__2));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__5(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__4));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__9(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__8));
v___x_592_ = l_Lean_stringToMessageData(v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__12(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__11));
v___x_597_ = l_Lean_MessageData_ofFormat(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object* v_funName_598_, lean_object* v_extraParams_599_, lean_object* v_tb_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
uint8_t v_synthetic_606_; 
v_synthetic_606_ = lean_ctor_get_uint8(v_tb_600_, sizeof(void*)*3 + 1);
if (v_synthetic_606_ == 0)
{
lean_object* v_ref_607_; lean_object* v_vars_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_ref_607_ = lean_ctor_get(v_tb_600_, 0);
v_vars_608_ = lean_ctor_get(v_tb_600_, 1);
v___x_609_ = lean_array_get_size(v_vars_608_);
v___x_610_ = lean_nat_dec_lt(v_extraParams_599_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec(v_extraParams_599_);
lean_dec(v_funName_598_);
v___x_611_ = lean_box(0);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_msg_623_; lean_object* v___x_624_; lean_object* v_ident_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_613_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_609_);
v___x_614_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__1, &l_Lean_Elab_TerminationBy_checkVars___closed__1_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__1);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
lean_inc(v_funName_598_);
v___x_616_ = l_Lean_MessageData_ofName(v_funName_598_);
v___x_617_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__3, &l_Lean_Elab_TerminationBy_checkVars___closed__3_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__3);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_599_);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__5, &l_Lean_Elab_TerminationBy_checkVars___closed__5_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__5);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v_msg_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_623_, 0, v___x_615_);
lean_ctor_set(v_msg_623_, 1, v___x_622_);
v___x_624_ = lean_unsigned_to_nat(0u);
v_ident_625_ = lean_array_fget_borrowed(v_vars_608_, v___x_624_);
v___x_626_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__7));
lean_inc(v_ident_625_);
v___x_627_ = l_Lean_Syntax_isOfKind(v_ident_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
lean_dec(v_funName_598_);
v___x_628_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_607_, v_msg_623_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = l_Lean_TSyntax_getId(v_ident_625_);
v___x_630_ = l_Lean_Name_isSuffixOf(v___x_629_, v_funName_598_);
lean_dec(v_funName_598_);
lean_dec(v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_607_, v_msg_623_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_msg_635_; lean_object* v___x_636_; 
v___x_632_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__9, &l_Lean_Elab_TerminationBy_checkVars___closed__9_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__9);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v_msg_623_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__12, &l_Lean_Elab_TerminationBy_checkVars___closed__12_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__12);
v_msg_635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_635_, 0, v___x_633_);
lean_ctor_set(v_msg_635_, 1, v___x_634_);
v___x_636_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_607_, v_msg_635_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
return v___x_636_;
}
}
}
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v_extraParams_599_);
lean_dec(v_funName_598_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object* v_funName_639_, lean_object* v_extraParams_640_, lean_object* v_tb_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Elab_TerminationBy_checkVars(v_funName_639_, v_extraParams_640_, v_tb_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec_ref(v_tb_641_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_object* v_00_u03b1_648_, lean_object* v_ref_649_, lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_649_, v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object* v_00_u03b1_657_, lean_object* v_ref_658_, lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(v_00_u03b1_657_, v_ref_658_, v_msg_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v_ref_658_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_object* v_00_u03b1_666_, lean_object* v_msg_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_674_, lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_674_, v_msg_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object* v_val_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v_val_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object* v_stx_684_, lean_object* v_terminationBy_x3f_x3f_685_, lean_object* v_terminationBy_x3f_686_, lean_object* v_partialFixpoint_x3f_687_, lean_object* v___x_688_, uint8_t v___x_689_, lean_object* v_toPure_690_, lean_object* v_decreasingBy_x3f_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_692_, 0, v_stx_684_);
lean_ctor_set(v___x_692_, 1, v_terminationBy_x3f_x3f_685_);
lean_ctor_set(v___x_692_, 2, v_terminationBy_x3f_686_);
lean_ctor_set(v___x_692_, 3, v_partialFixpoint_x3f_687_);
lean_ctor_set(v___x_692_, 4, v_decreasingBy_x3f_691_);
lean_ctor_set(v___x_692_, 5, v___x_688_);
lean_ctor_set_uint8(v___x_692_, sizeof(void*)*6, v___x_689_);
v___x_693_ = lean_apply_2(v_toPure_690_, lean_box(0), v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed(lean_object* v_stx_694_, lean_object* v_terminationBy_x3f_x3f_695_, lean_object* v_terminationBy_x3f_696_, lean_object* v_partialFixpoint_x3f_697_, lean_object* v___x_698_, lean_object* v___x_699_, lean_object* v_toPure_700_, lean_object* v_decreasingBy_x3f_701_){
_start:
{
uint8_t v___x_2913__boxed_702_; lean_object* v_res_703_; 
v___x_2913__boxed_702_ = lean_unbox(v___x_699_);
v_res_703_ = l_Lean_Elab_elabTerminationHints___redArg___lam__1(v_stx_694_, v_terminationBy_x3f_x3f_695_, v_terminationBy_x3f_696_, v_partialFixpoint_x3f_697_, v___x_698_, v___x_2913__boxed_702_, v_toPure_700_, v_decreasingBy_x3f_701_);
return v_res_703_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1));
v___x_707_ = l_Lean_stringToMessageData(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* v_stx_708_, lean_object* v_terminationBy_x3f_x3f_709_, lean_object* v_terminationBy_x3f_710_, lean_object* v___x_711_, uint8_t v___x_712_, lean_object* v_toPure_713_, lean_object* v_d_x3f_714_, lean_object* v_toBind_715_, lean_object* v_toFunctor_716_, lean_object* v___f_717_, lean_object* v___x_718_, lean_object* v___x_719_, lean_object* v___x_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v___x_723_, lean_object* v_partialFixpoint_x3f_724_){
_start:
{
lean_object* v___x_725_; lean_object* v___f_726_; 
v___x_725_ = lean_box(v___x_712_);
lean_inc(v_toPure_713_);
v___f_726_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_726_, 0, v_stx_708_);
lean_closure_set(v___f_726_, 1, v_terminationBy_x3f_x3f_709_);
lean_closure_set(v___f_726_, 2, v_terminationBy_x3f_710_);
lean_closure_set(v___f_726_, 3, v_partialFixpoint_x3f_724_);
lean_closure_set(v___f_726_, 4, v___x_711_);
lean_closure_set(v___f_726_, 5, v___x_725_);
lean_closure_set(v___f_726_, 6, v_toPure_713_);
if (lean_obj_tag(v_d_x3f_714_) == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_inst_721_);
lean_dec_ref(v___x_720_);
lean_dec_ref(v___x_719_);
lean_dec_ref(v___x_718_);
lean_dec_ref(v___f_717_);
lean_dec_ref(v_toFunctor_716_);
v___x_727_ = lean_box(0);
v___x_728_ = lean_apply_2(v_toPure_713_, lean_box(0), v___x_727_);
v___x_729_ = lean_apply_4(v_toBind_715_, lean_box(0), lean_box(0), v___x_728_, v___f_726_);
return v___x_729_;
}
else
{
lean_object* v_val_730_; lean_object* v_map_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_749_; 
v_val_730_ = lean_ctor_get(v_d_x3f_714_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v_d_x3f_714_, 1);
v_map_731_ = lean_ctor_get(v_toFunctor_716_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v_toFunctor_716_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v_toFunctor_716_, 1);
lean_dec(v_unused_750_);
v___x_733_ = v_toFunctor_716_;
v_isShared_734_ = v_isSharedCheck_749_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_map_731_);
lean_dec(v_toFunctor_716_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_749_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___y_736_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_739_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0));
v___x_740_ = l_Lean_Name_mkStr4(v___x_718_, v___x_719_, v___x_720_, v___x_739_);
lean_inc(v_val_730_);
v___x_741_ = l_Lean_Syntax_isOfKind(v_val_730_, v___x_740_);
lean_dec(v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
lean_del_object(v___x_733_);
lean_dec(v_toPure_713_);
v___x_742_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2, &l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2);
v___x_743_ = l_Lean_throwErrorAt___redArg(v_inst_721_, v_inst_722_, v_val_730_, v___x_742_);
v___y_736_ = v___x_743_;
goto v___jp_735_;
}
else
{
lean_object* v_tactic_744_; lean_object* v___x_746_; 
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_inst_721_);
v_tactic_744_ = l_Lean_Syntax_getArg(v_val_730_, v___x_723_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v_tactic_744_);
lean_ctor_set(v___x_733_, 0, v_val_730_);
v___x_746_ = v___x_733_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_val_730_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_tactic_744_);
v___x_746_ = v_reuseFailAlloc_748_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; 
v___x_747_ = lean_apply_2(v_toPure_713_, lean_box(0), v___x_746_);
v___y_736_ = v___x_747_;
goto v___jp_735_;
}
}
v___jp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_apply_4(v_map_731_, lean_box(0), lean_box(0), v___f_717_, v___y_736_);
v___x_738_ = lean_apply_4(v_toBind_715_, lean_box(0), lean_box(0), v___x_737_, v___f_726_);
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_stx_751_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_752_ = _args[1];
lean_object* v_terminationBy_x3f_753_ = _args[2];
lean_object* v___x_754_ = _args[3];
lean_object* v___x_755_ = _args[4];
lean_object* v_toPure_756_ = _args[5];
lean_object* v_d_x3f_757_ = _args[6];
lean_object* v_toBind_758_ = _args[7];
lean_object* v_toFunctor_759_ = _args[8];
lean_object* v___f_760_ = _args[9];
lean_object* v___x_761_ = _args[10];
lean_object* v___x_762_ = _args[11];
lean_object* v___x_763_ = _args[12];
lean_object* v_inst_764_ = _args[13];
lean_object* v_inst_765_ = _args[14];
lean_object* v___x_766_ = _args[15];
lean_object* v_partialFixpoint_x3f_767_ = _args[16];
_start:
{
uint8_t v___x_2931__boxed_768_; lean_object* v_res_769_; 
v___x_2931__boxed_768_ = lean_unbox(v___x_755_);
v_res_769_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_751_, v_terminationBy_x3f_x3f_752_, v_terminationBy_x3f_753_, v___x_754_, v___x_2931__boxed_768_, v_toPure_756_, v_d_x3f_757_, v_toBind_758_, v_toFunctor_759_, v___f_760_, v___x_761_, v___x_762_, v___x_763_, v_inst_764_, v_inst_765_, v___x_766_, v_partialFixpoint_x3f_767_);
lean_dec(v___x_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object* v___f_770_, lean_object* v_partialFixpoint_x3f_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = lean_apply_1(v___f_770_, v_partialFixpoint_x3f_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object* v_stx_776_, lean_object* v_terminationBy_x3f_x3f_777_, lean_object* v___x_778_, uint8_t v___x_779_, lean_object* v_toPure_780_, lean_object* v_d_x3f_781_, lean_object* v_toBind_782_, lean_object* v_toFunctor_783_, lean_object* v___f_784_, lean_object* v___x_785_, lean_object* v___x_786_, lean_object* v___x_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v___x_790_, lean_object* v_t_x3f_791_, lean_object* v_terminationBy_x3f_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___f_794_; 
v___x_793_ = lean_box(v___x_779_);
lean_inc(v___x_790_);
lean_inc_ref(v___x_787_);
lean_inc_ref(v___x_786_);
lean_inc_ref(v___x_785_);
lean_inc(v_toBind_782_);
lean_inc(v_toPure_780_);
v___f_794_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed), 17, 16);
lean_closure_set(v___f_794_, 0, v_stx_776_);
lean_closure_set(v___f_794_, 1, v_terminationBy_x3f_x3f_777_);
lean_closure_set(v___f_794_, 2, v_terminationBy_x3f_792_);
lean_closure_set(v___f_794_, 3, v___x_778_);
lean_closure_set(v___f_794_, 4, v___x_793_);
lean_closure_set(v___f_794_, 5, v_toPure_780_);
lean_closure_set(v___f_794_, 6, v_d_x3f_781_);
lean_closure_set(v___f_794_, 7, v_toBind_782_);
lean_closure_set(v___f_794_, 8, v_toFunctor_783_);
lean_closure_set(v___f_794_, 9, v___f_784_);
lean_closure_set(v___f_794_, 10, v___x_785_);
lean_closure_set(v___f_794_, 11, v___x_786_);
lean_closure_set(v___f_794_, 12, v___x_787_);
lean_closure_set(v___f_794_, 13, v_inst_788_);
lean_closure_set(v___f_794_, 14, v_inst_789_);
lean_closure_set(v___f_794_, 15, v___x_790_);
if (lean_obj_tag(v_t_x3f_791_) == 1)
{
lean_object* v_val_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_872_; 
v_val_795_ = lean_ctor_get(v_t_x3f_791_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v_t_x3f_791_);
if (v_isSharedCheck_872_ == 0)
{
v___x_797_ = v_t_x3f_791_;
v_isShared_798_ = v_isSharedCheck_872_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_val_795_);
lean_dec(v_t_x3f_791_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_872_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_799_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_787_);
lean_inc_ref(v___x_786_);
lean_inc_ref(v___x_785_);
v___x_800_ = l_Lean_Name_mkStr4(v___x_785_, v___x_786_, v___x_787_, v___x_799_);
lean_inc(v_val_795_);
v___x_801_ = l_Lean_Syntax_isOfKind(v_val_795_, v___x_800_);
lean_dec(v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_802_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_787_);
lean_inc_ref(v___x_786_);
lean_inc_ref(v___x_785_);
v___x_803_ = l_Lean_Name_mkStr4(v___x_785_, v___x_786_, v___x_787_, v___x_802_);
lean_inc(v_val_795_);
v___x_804_ = l_Lean_Syntax_isOfKind(v_val_795_, v___x_803_);
lean_dec(v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_805_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_806_ = l_Lean_Name_mkStr4(v___x_785_, v___x_786_, v___x_787_, v___x_805_);
lean_inc(v_val_795_);
v___x_807_ = l_Lean_Syntax_isOfKind(v_val_795_, v___x_806_);
lean_dec(v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_del_object(v___x_797_);
lean_dec(v_val_795_);
lean_dec(v___x_790_);
v___f_808_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_808_, 0, v___f_794_);
v___x_809_ = lean_box(0);
v___x_810_ = lean_apply_2(v_toPure_780_, lean_box(0), v___x_809_);
v___x_811_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v___x_810_, v___f_808_);
return v___x_811_;
}
else
{
lean_object* v___f_812_; lean_object* v_term_x3f_814_; lean_object* v___x_822_; uint8_t v___x_823_; 
v___f_812_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_812_, 0, v___f_794_);
v___x_822_ = l_Lean_Syntax_getArg(v_val_795_, v___x_790_);
v___x_823_ = l_Lean_Syntax_isNone(v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_822_);
v___x_825_ = l_Lean_Syntax_matchesNull(v___x_822_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec(v___x_822_);
lean_del_object(v___x_797_);
lean_dec(v_val_795_);
lean_dec(v___x_790_);
v___x_826_ = lean_box(0);
v___x_827_ = lean_apply_2(v_toPure_780_, lean_box(0), v___x_826_);
v___x_828_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v___x_827_, v___f_812_);
return v___x_828_;
}
else
{
lean_object* v_term_x3f_829_; lean_object* v___x_830_; 
v_term_x3f_829_ = l_Lean_Syntax_getArg(v___x_822_, v___x_790_);
lean_dec(v___x_790_);
lean_dec(v___x_822_);
v___x_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_830_, 0, v_term_x3f_829_);
v_term_x3f_814_ = v___x_830_;
goto v___jp_813_;
}
}
else
{
lean_object* v___x_831_; 
lean_dec(v___x_822_);
lean_dec(v___x_790_);
v___x_831_ = lean_box(0);
v_term_x3f_814_ = v___x_831_;
goto v___jp_813_;
}
v___jp_813_:
{
uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_815_ = 2;
v___x_816_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_816_, 0, v_val_795_);
lean_ctor_set(v___x_816_, 1, v_term_x3f_814_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*2, v___x_815_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_816_);
v___x_818_ = v___x_797_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_821_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_apply_2(v_toPure_780_, lean_box(0), v___x_818_);
v___x_820_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v___x_819_, v___f_812_);
return v___x_820_;
}
}
}
}
else
{
lean_object* v___f_832_; lean_object* v_term_x3f_834_; lean_object* v___x_842_; uint8_t v___x_843_; 
lean_dec_ref(v___x_787_);
lean_dec_ref(v___x_786_);
lean_dec_ref(v___x_785_);
v___f_832_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_832_, 0, v___f_794_);
v___x_842_ = l_Lean_Syntax_getArg(v_val_795_, v___x_790_);
v___x_843_ = l_Lean_Syntax_isNone(v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_842_);
v___x_845_ = l_Lean_Syntax_matchesNull(v___x_842_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec(v___x_842_);
lean_del_object(v___x_797_);
lean_dec(v_val_795_);
lean_dec(v___x_790_);
v___x_846_ = lean_box(0);
v___x_847_ = lean_apply_2(v_toPure_780_, lean_box(0), v___x_846_);
v___x_848_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v___x_847_, v___f_832_);
return v___x_848_;
}
else
{
lean_object* v_term_x3f_849_; lean_object* v___x_850_; 
v_term_x3f_849_ = l_Lean_Syntax_getArg(v___x_842_, v___x_790_);
lean_dec(v___x_790_);
lean_dec(v___x_842_);
v___x_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_850_, 0, v_term_x3f_849_);
v_term_x3f_834_ = v___x_850_;
goto v___jp_833_;
}
}
else
{
lean_object* v___x_851_; 
lean_dec(v___x_842_);
lean_dec(v___x_790_);
v___x_851_ = lean_box(0);
v_term_x3f_834_ = v___x_851_;
goto v___jp_833_;
}
v___jp_833_:
{
uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_835_ = 1;
v___x_836_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_836_, 0, v_val_795_);
lean_ctor_set(v___x_836_, 1, v_term_x3f_834_);
lean_ctor_set_uint8(v___x_836_, sizeof(void*)*2, v___x_835_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_836_);
v___x_838_ = v___x_797_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_841_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_apply_2(v_toPure_780_, lean_box(0), v___x_838_);
v___x_840_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v___x_839_, v___f_832_);
return v___x_840_;
}
}
}
}
else
{
lean_object* v___f_852_; lean_object* v_term_x3f_854_; lean_object* v___x_862_; uint8_t v___x_863_; 
lean_dec_ref(v___x_787_);
lean_dec_ref(v___x_786_);
lean_dec_ref(v___x_785_);
v___f_852_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_852_, 0, v___f_794_);
v___x_862_ = l_Lean_Syntax_getArg(v_val_795_, v___x_790_);
v___x_863_ = l_Lean_Syntax_isNone(v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_862_);
v___x_865_ = l_Lean_Syntax_matchesNull(v___x_862_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec(v___x_862_);
lean_del_object(v___x_797_);
lean_dec(v_val_795_);
lean_dec(v___x_790_);
v___x_866_ = lean_box(0);
v___x_867_ = lean_apply_2(v_toPure_780_, lean_box(0), v___x_866_);
v___x_868_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v___x_867_, v___f_852_);
return v___x_868_;
}
else
{
lean_object* v_term_x3f_869_; lean_object* v___x_870_; 
v_term_x3f_869_ = l_Lean_Syntax_getArg(v___x_862_, v___x_790_);
lean_dec(v___x_790_);
lean_dec(v___x_862_);
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v_term_x3f_869_);
v_term_x3f_854_ = v___x_870_;
goto v___jp_853_;
}
}
else
{
lean_object* v___x_871_; 
lean_dec(v___x_862_);
lean_dec(v___x_790_);
v___x_871_ = lean_box(0);
v_term_x3f_854_ = v___x_871_;
goto v___jp_853_;
}
v___jp_853_:
{
uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_855_ = 0;
v___x_856_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_856_, 0, v_val_795_);
lean_ctor_set(v___x_856_, 1, v_term_x3f_854_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*2, v___x_855_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_856_);
v___x_858_ = v___x_797_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_861_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_apply_2(v_toPure_780_, lean_box(0), v___x_858_);
v___x_860_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v___x_859_, v___f_852_);
return v___x_860_;
}
}
}
}
}
else
{
lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v_t_x3f_791_);
lean_dec(v___x_790_);
lean_dec_ref(v___x_787_);
lean_dec_ref(v___x_786_);
lean_dec_ref(v___x_785_);
v___f_873_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_873_, 0, v___f_794_);
v___x_874_ = lean_box(0);
v___x_875_ = lean_apply_2(v_toPure_780_, lean_box(0), v___x_874_);
v___x_876_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v___x_875_, v___f_873_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_stx_877_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_878_ = _args[1];
lean_object* v___x_879_ = _args[2];
lean_object* v___x_880_ = _args[3];
lean_object* v_toPure_881_ = _args[4];
lean_object* v_d_x3f_882_ = _args[5];
lean_object* v_toBind_883_ = _args[6];
lean_object* v_toFunctor_884_ = _args[7];
lean_object* v___f_885_ = _args[8];
lean_object* v___x_886_ = _args[9];
lean_object* v___x_887_ = _args[10];
lean_object* v___x_888_ = _args[11];
lean_object* v_inst_889_ = _args[12];
lean_object* v_inst_890_ = _args[13];
lean_object* v___x_891_ = _args[14];
lean_object* v_t_x3f_892_ = _args[15];
lean_object* v_terminationBy_x3f_893_ = _args[16];
_start:
{
uint8_t v___x_3020__boxed_894_; lean_object* v_res_895_; 
v___x_3020__boxed_894_ = lean_unbox(v___x_880_);
v_res_895_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11(v_stx_877_, v_terminationBy_x3f_x3f_878_, v___x_879_, v___x_3020__boxed_894_, v_toPure_881_, v_d_x3f_882_, v_toBind_883_, v_toFunctor_884_, v___f_885_, v___x_886_, v___x_887_, v___x_888_, v_inst_889_, v_inst_890_, v___x_891_, v_t_x3f_892_, v_terminationBy_x3f_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* v___f_896_, lean_object* v_terminationBy_x3f_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_apply_1(v___f_896_, v_terminationBy_x3f_897_);
return v___x_898_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* v_stx_907_, lean_object* v___x_908_, uint8_t v___x_909_, lean_object* v_toPure_910_, lean_object* v_d_x3f_911_, lean_object* v_toBind_912_, lean_object* v_toFunctor_913_, lean_object* v___f_914_, lean_object* v___x_915_, lean_object* v___x_916_, lean_object* v___x_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v___x_920_, lean_object* v_t_x3f_921_, lean_object* v_terminationBy_x3f_x3f_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___f_924_; 
v___x_923_ = lean_box(v___x_909_);
lean_inc(v_t_x3f_921_);
lean_inc(v___x_920_);
lean_inc_ref(v_inst_919_);
lean_inc_ref(v_inst_918_);
lean_inc_ref(v___x_917_);
lean_inc_ref(v___x_916_);
lean_inc_ref(v___x_915_);
lean_inc(v_toBind_912_);
lean_inc(v_toPure_910_);
lean_inc(v___x_908_);
v___f_924_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_924_, 0, v_stx_907_);
lean_closure_set(v___f_924_, 1, v_terminationBy_x3f_x3f_922_);
lean_closure_set(v___f_924_, 2, v___x_908_);
lean_closure_set(v___f_924_, 3, v___x_923_);
lean_closure_set(v___f_924_, 4, v_toPure_910_);
lean_closure_set(v___f_924_, 5, v_d_x3f_911_);
lean_closure_set(v___f_924_, 6, v_toBind_912_);
lean_closure_set(v___f_924_, 7, v_toFunctor_913_);
lean_closure_set(v___f_924_, 8, v___f_914_);
lean_closure_set(v___f_924_, 9, v___x_915_);
lean_closure_set(v___f_924_, 10, v___x_916_);
lean_closure_set(v___f_924_, 11, v___x_917_);
lean_closure_set(v___f_924_, 12, v_inst_918_);
lean_closure_set(v___f_924_, 13, v_inst_919_);
lean_closure_set(v___f_924_, 14, v___x_920_);
lean_closure_set(v___f_924_, 15, v_t_x3f_921_);
if (lean_obj_tag(v_t_x3f_921_) == 1)
{
lean_object* v_val_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_1037_; 
v_val_925_ = lean_ctor_get(v_t_x3f_921_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_t_x3f_921_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_927_ = v_t_x3f_921_;
v_isShared_928_ = v_isSharedCheck_1037_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_val_925_);
lean_dec(v_t_x3f_921_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_1037_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_929_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0));
lean_inc_ref(v___x_917_);
lean_inc_ref(v___x_916_);
lean_inc_ref(v___x_915_);
v___x_930_ = l_Lean_Name_mkStr4(v___x_915_, v___x_916_, v___x_917_, v___x_929_);
lean_inc(v_val_925_);
v___x_931_ = l_Lean_Syntax_isOfKind(v_val_925_, v___x_930_);
lean_dec(v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
lean_del_object(v___x_927_);
lean_dec(v___x_908_);
v___x_932_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1));
lean_inc_ref(v___x_917_);
lean_inc_ref(v___x_916_);
lean_inc_ref(v___x_915_);
v___x_933_ = l_Lean_Name_mkStr4(v___x_915_, v___x_916_, v___x_917_, v___x_932_);
lean_inc(v_val_925_);
v___x_934_ = l_Lean_Syntax_isOfKind(v_val_925_, v___x_933_);
lean_dec(v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_935_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_917_);
lean_inc_ref(v___x_916_);
lean_inc_ref(v___x_915_);
v___x_936_ = l_Lean_Name_mkStr4(v___x_915_, v___x_916_, v___x_917_, v___x_935_);
lean_inc(v_val_925_);
v___x_937_ = l_Lean_Syntax_isOfKind(v_val_925_, v___x_936_);
lean_dec(v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_938_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_917_);
lean_inc_ref(v___x_916_);
lean_inc_ref(v___x_915_);
v___x_939_ = l_Lean_Name_mkStr4(v___x_915_, v___x_916_, v___x_917_, v___x_938_);
lean_inc(v_val_925_);
v___x_940_ = l_Lean_Syntax_isOfKind(v_val_925_, v___x_939_);
lean_dec(v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_941_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_942_ = l_Lean_Name_mkStr4(v___x_915_, v___x_916_, v___x_917_, v___x_941_);
lean_inc(v_val_925_);
v___x_943_ = l_Lean_Syntax_isOfKind(v_val_925_, v___x_942_);
lean_dec(v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___f_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec(v___x_920_);
lean_dec(v_toPure_910_);
v___f_944_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_944_, 0, v___f_924_);
v___x_945_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_946_ = l_Lean_throwErrorAt___redArg(v_inst_918_, v_inst_919_, v_val_925_, v___x_945_);
v___x_947_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_946_, v___f_944_);
return v___x_947_;
}
else
{
lean_object* v___f_948_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___f_948_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_948_, 0, v___f_924_);
v___x_953_ = l_Lean_Syntax_getArg(v_val_925_, v___x_920_);
lean_dec(v___x_920_);
v___x_954_ = l_Lean_Syntax_isNone(v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = lean_unsigned_to_nat(2u);
v___x_956_ = l_Lean_Syntax_matchesNull(v___x_953_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v_toPure_910_);
v___x_957_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_958_ = l_Lean_throwErrorAt___redArg(v_inst_918_, v_inst_919_, v_val_925_, v___x_957_);
v___x_959_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_958_, v___f_948_);
return v___x_959_;
}
else
{
lean_dec(v_val_925_);
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
goto v___jp_949_;
}
}
else
{
lean_dec(v___x_953_);
lean_dec(v_val_925_);
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
goto v___jp_949_;
}
v___jp_949_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_box(0);
v___x_951_ = lean_apply_2(v_toPure_910_, lean_box(0), v___x_950_);
v___x_952_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_951_, v___f_948_);
return v___x_952_;
}
}
}
else
{
lean_object* v___f_960_; lean_object* v___x_965_; uint8_t v___x_966_; 
lean_dec_ref(v___x_917_);
lean_dec_ref(v___x_916_);
lean_dec_ref(v___x_915_);
v___f_960_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_960_, 0, v___f_924_);
v___x_965_ = l_Lean_Syntax_getArg(v_val_925_, v___x_920_);
lean_dec(v___x_920_);
v___x_966_ = l_Lean_Syntax_isNone(v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = lean_unsigned_to_nat(2u);
v___x_968_ = l_Lean_Syntax_matchesNull(v___x_965_, v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec(v_toPure_910_);
v___x_969_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_970_ = l_Lean_throwErrorAt___redArg(v_inst_918_, v_inst_919_, v_val_925_, v___x_969_);
v___x_971_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_970_, v___f_960_);
return v___x_971_;
}
else
{
lean_dec(v_val_925_);
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
goto v___jp_961_;
}
}
else
{
lean_dec(v___x_965_);
lean_dec(v_val_925_);
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
goto v___jp_961_;
}
v___jp_961_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_box(0);
v___x_963_ = lean_apply_2(v_toPure_910_, lean_box(0), v___x_962_);
v___x_964_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_963_, v___f_960_);
return v___x_964_;
}
}
}
else
{
lean_object* v___f_972_; lean_object* v___x_977_; uint8_t v___x_978_; 
lean_dec_ref(v___x_917_);
lean_dec_ref(v___x_916_);
lean_dec_ref(v___x_915_);
v___f_972_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_972_, 0, v___f_924_);
v___x_977_ = l_Lean_Syntax_getArg(v_val_925_, v___x_920_);
lean_dec(v___x_920_);
v___x_978_ = l_Lean_Syntax_isNone(v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = lean_unsigned_to_nat(2u);
v___x_980_ = l_Lean_Syntax_matchesNull(v___x_977_, v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec(v_toPure_910_);
v___x_981_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_982_ = l_Lean_throwErrorAt___redArg(v_inst_918_, v_inst_919_, v_val_925_, v___x_981_);
v___x_983_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_982_, v___f_972_);
return v___x_983_;
}
else
{
lean_dec(v_val_925_);
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
goto v___jp_973_;
}
}
else
{
lean_dec(v___x_977_);
lean_dec(v_val_925_);
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
goto v___jp_973_;
}
v___jp_973_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_box(0);
v___x_975_ = lean_apply_2(v_toPure_910_, lean_box(0), v___x_974_);
v___x_976_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_975_, v___f_972_);
return v___x_976_;
}
}
}
else
{
lean_object* v___f_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec(v_val_925_);
lean_dec(v___x_920_);
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
lean_dec_ref(v___x_917_);
lean_dec_ref(v___x_916_);
lean_dec_ref(v___x_915_);
v___f_984_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_984_, 0, v___f_924_);
v___x_985_ = lean_box(0);
v___x_986_ = lean_apply_2(v_toPure_910_, lean_box(0), v___x_985_);
v___x_987_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_986_, v___f_984_);
return v___x_987_;
}
}
else
{
lean_object* v___f_988_; uint8_t v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; uint8_t v___y_993_; lean_object* v___y_1001_; uint8_t v___y_1002_; uint8_t v___y_1003_; lean_object* v_s_1010_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
lean_dec_ref(v___x_917_);
lean_dec_ref(v___x_916_);
lean_dec_ref(v___x_915_);
v___f_988_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_988_, 0, v___f_924_);
v___x_1028_ = l_Lean_Syntax_getArg(v_val_925_, v___x_920_);
v___x_1029_ = l_Lean_Syntax_isNone(v___x_1028_);
if (v___x_1029_ == 0)
{
uint8_t v___x_1030_; 
lean_inc(v___x_1028_);
v___x_1030_ = l_Lean_Syntax_matchesNull(v___x_1028_, v___x_920_);
lean_dec(v___x_920_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec(v___x_1028_);
lean_del_object(v___x_927_);
lean_dec(v_toPure_910_);
lean_dec(v___x_908_);
v___x_1031_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1032_ = l_Lean_throwErrorAt___redArg(v_inst_918_, v_inst_919_, v_val_925_, v___x_1031_);
v___x_1033_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_1032_, v___f_988_);
return v___x_1033_;
}
else
{
lean_object* v_s_1034_; lean_object* v___x_1035_; 
v_s_1034_ = l_Lean_Syntax_getArg(v___x_1028_, v___x_908_);
lean_dec(v___x_1028_);
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_s_1034_);
v_s_1010_ = v___x_1035_;
goto v___jp_1009_;
}
}
else
{
lean_object* v___x_1036_; 
lean_dec(v___x_1028_);
lean_dec(v___x_920_);
v___x_1036_ = lean_box(0);
v_s_1010_ = v___x_1036_;
goto v___jp_1009_;
}
v___jp_989_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_994_, 0, v_val_925_);
lean_ctor_set(v___x_994_, 1, v___y_992_);
lean_ctor_set(v___x_994_, 2, v___y_991_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*3, v___y_993_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*3 + 1, v___y_990_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_994_);
v___x_996_ = v___x_927_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_999_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_apply_2(v_toPure_910_, lean_box(0), v___x_996_);
v___x_998_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_997_, v___f_988_);
return v___x_998_;
}
}
v___jp_1000_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1004_ = lean_mk_empty_array_with_capacity(v___x_908_);
lean_dec(v___x_908_);
v___x_1005_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1005_, 0, v_val_925_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
lean_ctor_set(v___x_1005_, 2, v___y_1001_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*3, v___y_1003_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*3 + 1, v___y_1002_);
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
v___x_1007_ = lean_apply_2(v_toPure_910_, lean_box(0), v___x_1006_);
v___x_1008_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_1007_, v___f_988_);
return v___x_1008_;
}
v___jp_1009_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1011_ = lean_unsigned_to_nat(2u);
v___x_1012_ = l_Lean_Syntax_getArg(v_val_925_, v___x_1011_);
lean_inc(v___x_1012_);
v___x_1013_ = l_Lean_Syntax_matchesNull(v___x_1012_, v___x_1011_);
if (v___x_1013_ == 0)
{
uint8_t v___x_1014_; 
lean_del_object(v___x_927_);
v___x_1014_ = l_Lean_Syntax_matchesNull(v___x_1012_, v___x_908_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v_s_1010_);
lean_dec(v_toPure_910_);
lean_dec(v___x_908_);
v___x_1015_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1016_ = l_Lean_throwErrorAt___redArg(v_inst_918_, v_inst_919_, v_val_925_, v___x_1015_);
v___x_1017_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_1016_, v___f_988_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; lean_object* v_body_1019_; 
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
v___x_1018_ = lean_unsigned_to_nat(3u);
v_body_1019_ = l_Lean_Syntax_getArg(v_val_925_, v___x_1018_);
if (lean_obj_tag(v_s_1010_) == 0)
{
v___y_1001_ = v_body_1019_;
v___y_1002_ = v___x_1013_;
v___y_1003_ = v___x_1013_;
goto v___jp_1000_;
}
else
{
lean_dec_ref_known(v_s_1010_, 1);
v___y_1001_ = v_body_1019_;
v___y_1002_ = v___x_1013_;
v___y_1003_ = v___x_1014_;
goto v___jp_1000_;
}
}
}
else
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = l_Lean_Syntax_getArg(v___x_1012_, v___x_908_);
lean_dec(v___x_1012_);
lean_inc(v___x_1020_);
v___x_1021_ = l_Lean_Syntax_matchesNull(v___x_1020_, v___x_908_);
lean_dec(v___x_908_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v_body_1023_; lean_object* v_vars_1024_; 
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
v___x_1022_ = lean_unsigned_to_nat(3u);
v_body_1023_ = l_Lean_Syntax_getArg(v_val_925_, v___x_1022_);
v_vars_1024_ = l_Lean_Syntax_getArgs(v___x_1020_);
lean_dec(v___x_1020_);
if (lean_obj_tag(v_s_1010_) == 0)
{
v___y_990_ = v___x_1021_;
v___y_991_ = v_body_1023_;
v___y_992_ = v_vars_1024_;
v___y_993_ = v___x_1021_;
goto v___jp_989_;
}
else
{
lean_dec_ref_known(v_s_1010_, 1);
v___y_990_ = v___x_1021_;
v___y_991_ = v_body_1023_;
v___y_992_ = v_vars_1024_;
v___y_993_ = v___x_1013_;
goto v___jp_989_;
}
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec(v___x_1020_);
lean_dec(v_s_1010_);
lean_del_object(v___x_927_);
lean_dec(v_toPure_910_);
v___x_1025_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
v___x_1026_ = l_Lean_throwErrorAt___redArg(v_inst_918_, v_inst_919_, v_val_925_, v___x_1025_);
v___x_1027_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_1026_, v___f_988_);
return v___x_1027_;
}
}
}
}
}
}
else
{
lean_object* v___f_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec(v_t_x3f_921_);
lean_dec(v___x_920_);
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
lean_dec_ref(v___x_917_);
lean_dec_ref(v___x_916_);
lean_dec_ref(v___x_915_);
lean_dec(v___x_908_);
v___f_1038_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1038_, 0, v___f_924_);
v___x_1039_ = lean_box(0);
v___x_1040_ = lean_apply_2(v_toPure_910_, lean_box(0), v___x_1039_);
v___x_1041_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_1040_, v___f_1038_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed(lean_object* v_stx_1042_, lean_object* v___x_1043_, lean_object* v___x_1044_, lean_object* v_toPure_1045_, lean_object* v_d_x3f_1046_, lean_object* v_toBind_1047_, lean_object* v_toFunctor_1048_, lean_object* v___f_1049_, lean_object* v___x_1050_, lean_object* v___x_1051_, lean_object* v___x_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v___x_1055_, lean_object* v_t_x3f_1056_, lean_object* v_terminationBy_x3f_x3f_1057_){
_start:
{
uint8_t v___x_3244__boxed_1058_; lean_object* v_res_1059_; 
v___x_3244__boxed_1058_ = lean_unbox(v___x_1044_);
v_res_1059_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19(v_stx_1042_, v___x_1043_, v___x_3244__boxed_1058_, v_toPure_1045_, v_d_x3f_1046_, v_toBind_1047_, v_toFunctor_1048_, v___f_1049_, v___x_1050_, v___x_1051_, v___x_1052_, v_inst_1053_, v_inst_1054_, v___x_1055_, v_t_x3f_1056_, v_terminationBy_x3f_x3f_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* v___f_1060_, lean_object* v_terminationBy_x3f_x3f_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_apply_1(v___f_1060_, v_terminationBy_x3f_x3f_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_stx_1087_){
_start:
{
if (lean_obj_tag(v_stx_1087_) == 0)
{
lean_object* v_toApplicative_1088_; lean_object* v_toPure_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_toApplicative_1088_ = lean_ctor_get(v_inst_1085_, 0);
lean_inc_ref(v_toApplicative_1088_);
lean_dec_ref(v_inst_1086_);
lean_dec_ref(v_inst_1085_);
v_toPure_1089_ = lean_ctor_get(v_toApplicative_1088_, 1);
lean_inc(v_toPure_1089_);
lean_dec_ref(v_toApplicative_1088_);
v___x_1090_ = 1;
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1093_, 0, v_stx_1087_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
lean_ctor_set(v___x_1093_, 2, v___x_1092_);
lean_ctor_set(v___x_1093_, 3, v___x_1092_);
lean_ctor_set(v___x_1093_, 4, v___x_1092_);
lean_ctor_set(v___x_1093_, 5, v___x_1091_);
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*6, v___x_1090_);
v___x_1094_ = lean_apply_2(v_toPure_1089_, lean_box(0), v___x_1093_);
return v___x_1094_;
}
else
{
lean_object* v_toApplicative_1095_; lean_object* v_toBind_1096_; lean_object* v_toFunctor_1097_; lean_object* v_toPure_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_toApplicative_1095_ = lean_ctor_get(v_inst_1085_, 0);
v_toBind_1096_ = lean_ctor_get(v_inst_1085_, 1);
v_toFunctor_1097_ = lean_ctor_get(v_toApplicative_1095_, 0);
v_toPure_1098_ = lean_ctor_get(v_toApplicative_1095_, 1);
v___x_1099_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__0));
v___x_1100_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__1));
v___x_1101_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__2));
v___x_1102_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__4));
lean_inc(v_stx_1087_);
v___x_1103_ = l_Lean_Syntax_isOfKind(v_stx_1087_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1104_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1105_ = lean_box(0);
lean_inc_n(v_stx_1087_, 2);
v___x_1106_ = l_Lean_Syntax_formatStx(v_stx_1087_, v___x_1105_, v___x_1103_);
v___x_1107_ = l_Std_Format_defWidth;
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = l_Std_Format_pretty(v___x_1106_, v___x_1107_, v___x_1108_, v___x_1108_);
v___x_1110_ = lean_string_append(v___x_1104_, v___x_1109_);
lean_dec_ref(v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1112_ = lean_string_append(v___x_1110_, v___x_1111_);
v___x_1113_ = l_Lean_Syntax_getKind(v_stx_1087_);
v___x_1114_ = 1;
v___x_1115_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1113_, v___x_1114_);
v___x_1116_ = lean_string_append(v___x_1112_, v___x_1115_);
lean_dec_ref(v___x_1115_);
v___x_1117_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
v___x_1118_ = l_Lean_MessageData_ofFormat(v___x_1117_);
v___x_1119_ = l_Lean_throwErrorAt___redArg(v_inst_1085_, v_inst_1086_, v_stx_1087_, v___x_1118_);
return v___x_1119_;
}
else
{
lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v_d_x3f_1126_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v_t_x3f_1157_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___f_1120_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__7));
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1194_ = l_Lean_Syntax_getArg(v_stx_1087_, v___x_1121_);
v___x_1195_ = l_Lean_Syntax_isNone(v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1194_);
v___x_1197_ = l_Lean_Syntax_matchesNull(v___x_1194_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec(v___x_1194_);
v___x_1198_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1199_ = lean_box(0);
lean_inc_n(v_stx_1087_, 2);
v___x_1200_ = l_Lean_Syntax_formatStx(v_stx_1087_, v___x_1199_, v___x_1197_);
v___x_1201_ = l_Std_Format_defWidth;
v___x_1202_ = l_Std_Format_pretty(v___x_1200_, v___x_1201_, v___x_1121_, v___x_1121_);
v___x_1203_ = lean_string_append(v___x_1198_, v___x_1202_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1205_ = lean_string_append(v___x_1203_, v___x_1204_);
v___x_1206_ = l_Lean_Syntax_getKind(v_stx_1087_);
v___x_1207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1206_, v___x_1103_);
v___x_1208_ = lean_string_append(v___x_1205_, v___x_1207_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
v___x_1210_ = l_Lean_MessageData_ofFormat(v___x_1209_);
v___x_1211_ = l_Lean_throwErrorAt___redArg(v_inst_1085_, v_inst_1086_, v_stx_1087_, v___x_1210_);
return v___x_1211_;
}
else
{
lean_object* v_t_x3f_1212_; lean_object* v___x_1213_; 
v_t_x3f_1212_ = l_Lean_Syntax_getArg(v___x_1194_, v___x_1121_);
lean_dec(v___x_1194_);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_t_x3f_1212_);
v_t_x3f_1157_ = v___x_1213_;
goto v___jp_1156_;
}
}
else
{
lean_object* v___x_1214_; 
lean_dec(v___x_1194_);
v___x_1214_ = lean_box(0);
v_t_x3f_1157_ = v___x_1214_;
goto v___jp_1156_;
}
v___jp_1122_:
{
lean_object* v___x_1127_; lean_object* v___f_1128_; 
v___x_1127_ = lean_box(v___x_1103_);
lean_inc(v_toBind_1096_);
lean_inc(v_toPure_1098_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed), 16, 15);
lean_closure_set(v___f_1128_, 0, v_stx_1087_);
lean_closure_set(v___f_1128_, 1, v___x_1121_);
lean_closure_set(v___f_1128_, 2, v___x_1127_);
lean_closure_set(v___f_1128_, 3, v_toPure_1098_);
lean_closure_set(v___f_1128_, 4, v_d_x3f_1126_);
lean_closure_set(v___f_1128_, 5, v_toBind_1096_);
lean_closure_set(v___f_1128_, 6, v_toFunctor_1097_);
lean_closure_set(v___f_1128_, 7, v___f_1120_);
lean_closure_set(v___f_1128_, 8, v___x_1099_);
lean_closure_set(v___f_1128_, 9, v___x_1100_);
lean_closure_set(v___f_1128_, 10, v___x_1101_);
lean_closure_set(v___f_1128_, 11, v_inst_1085_);
lean_closure_set(v___f_1128_, 12, v_inst_1086_);
lean_closure_set(v___f_1128_, 13, v___y_1124_);
lean_closure_set(v___f_1128_, 14, v___y_1123_);
if (lean_obj_tag(v___y_1125_) == 1)
{
lean_object* v_val_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1145_; 
v_val_1129_ = lean_ctor_get(v___y_1125_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___y_1125_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1131_ = v___y_1125_;
v_isShared_1132_ = v_isSharedCheck_1145_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_val_1129_);
lean_dec(v___y_1125_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1145_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__8));
lean_inc(v_val_1129_);
v___x_1134_ = l_Lean_Syntax_isOfKind(v_val_1129_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___f_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_del_object(v___x_1131_);
lean_dec(v_val_1129_);
v___f_1135_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1135_, 0, v___f_1128_);
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_apply_2(v_toPure_1098_, lean_box(0), v___x_1136_);
v___x_1138_ = lean_apply_4(v_toBind_1096_, lean_box(0), lean_box(0), v___x_1137_, v___f_1135_);
return v___x_1138_;
}
else
{
lean_object* v___f_1139_; lean_object* v___x_1141_; 
v___f_1139_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1139_, 0, v___f_1128_);
if (v_isShared_1132_ == 0)
{
v___x_1141_ = v___x_1131_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_val_1129_);
v___x_1141_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_apply_2(v_toPure_1098_, lean_box(0), v___x_1141_);
v___x_1143_ = lean_apply_4(v_toBind_1096_, lean_box(0), lean_box(0), v___x_1142_, v___f_1139_);
return v___x_1143_;
}
}
}
}
else
{
lean_object* v___f_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec(v___y_1125_);
v___f_1146_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1146_, 0, v___f_1128_);
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_apply_2(v_toPure_1098_, lean_box(0), v___x_1147_);
v___x_1149_ = lean_apply_4(v_toBind_1096_, lean_box(0), lean_box(0), v___x_1148_, v___f_1146_);
return v___x_1149_;
}
}
v___jp_1150_:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___y_1154_);
v___y_1123_ = v___y_1151_;
v___y_1124_ = v___y_1152_;
v___y_1125_ = v___y_1153_;
v_d_x3f_1126_ = v___x_1155_;
goto v___jp_1122_;
}
v___jp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = l_Lean_Syntax_getArg(v_stx_1087_, v___x_1158_);
v___x_1160_ = l_Lean_Syntax_isNone(v___x_1159_);
if (v___x_1160_ == 0)
{
uint8_t v___x_1161_; 
lean_inc(v___x_1159_);
v___x_1161_ = l_Lean_Syntax_matchesNull(v___x_1159_, v___x_1158_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec(v___x_1159_);
lean_dec(v_t_x3f_1157_);
v___x_1162_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1163_ = lean_box(0);
lean_inc_n(v_stx_1087_, 2);
v___x_1164_ = l_Lean_Syntax_formatStx(v_stx_1087_, v___x_1163_, v___x_1161_);
v___x_1165_ = l_Std_Format_defWidth;
v___x_1166_ = l_Std_Format_pretty(v___x_1164_, v___x_1165_, v___x_1121_, v___x_1121_);
v___x_1167_ = lean_string_append(v___x_1162_, v___x_1166_);
lean_dec_ref(v___x_1166_);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1169_ = lean_string_append(v___x_1167_, v___x_1168_);
v___x_1170_ = l_Lean_Syntax_getKind(v_stx_1087_);
v___x_1171_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1170_, v___x_1103_);
v___x_1172_ = lean_string_append(v___x_1169_, v___x_1171_);
lean_dec_ref(v___x_1171_);
v___x_1173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
v___x_1174_ = l_Lean_MessageData_ofFormat(v___x_1173_);
v___x_1175_ = l_Lean_throwErrorAt___redArg(v_inst_1085_, v_inst_1086_, v_stx_1087_, v___x_1174_);
return v___x_1175_;
}
else
{
lean_object* v_d_x3f_1176_; 
v_d_x3f_1176_ = l_Lean_Syntax_getArg(v___x_1159_, v___x_1121_);
lean_dec(v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__9));
lean_inc(v_d_x3f_1176_);
v___x_1178_ = l_Lean_Syntax_isOfKind(v_d_x3f_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec(v_d_x3f_1176_);
lean_dec(v_t_x3f_1157_);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1180_ = lean_box(0);
lean_inc_n(v_stx_1087_, 2);
v___x_1181_ = l_Lean_Syntax_formatStx(v_stx_1087_, v___x_1180_, v___x_1160_);
v___x_1182_ = l_Std_Format_defWidth;
v___x_1183_ = l_Std_Format_pretty(v___x_1181_, v___x_1182_, v___x_1121_, v___x_1121_);
v___x_1184_ = lean_string_append(v___x_1179_, v___x_1183_);
lean_dec_ref(v___x_1183_);
v___x_1185_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1186_ = lean_string_append(v___x_1184_, v___x_1185_);
v___x_1187_ = l_Lean_Syntax_getKind(v_stx_1087_);
v___x_1188_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1187_, v___x_1161_);
v___x_1189_ = lean_string_append(v___x_1186_, v___x_1188_);
lean_dec_ref(v___x_1188_);
v___x_1190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
v___x_1191_ = l_Lean_MessageData_ofFormat(v___x_1190_);
v___x_1192_ = l_Lean_throwErrorAt___redArg(v_inst_1085_, v_inst_1086_, v_stx_1087_, v___x_1191_);
return v___x_1192_;
}
else
{
lean_inc(v_toPure_1098_);
lean_inc_ref(v_toFunctor_1097_);
lean_inc(v_toBind_1096_);
lean_inc(v_t_x3f_1157_);
v___y_1151_ = v_t_x3f_1157_;
v___y_1152_ = v___x_1158_;
v___y_1153_ = v_t_x3f_1157_;
v___y_1154_ = v_d_x3f_1176_;
goto v___jp_1150_;
}
}
else
{
lean_inc(v_toPure_1098_);
lean_inc_ref(v_toFunctor_1097_);
lean_inc(v_toBind_1096_);
lean_inc(v_t_x3f_1157_);
v___y_1151_ = v_t_x3f_1157_;
v___y_1152_ = v___x_1158_;
v___y_1153_ = v_t_x3f_1157_;
v___y_1154_ = v_d_x3f_1176_;
goto v___jp_1150_;
}
}
}
else
{
lean_object* v___x_1193_; 
lean_inc(v_toPure_1098_);
lean_inc_ref(v_toFunctor_1097_);
lean_inc(v_toBind_1096_);
lean_dec(v___x_1159_);
v___x_1193_ = lean_box(0);
lean_inc(v_t_x3f_1157_);
v___y_1123_ = v_t_x3f_1157_;
v___y_1124_ = v___x_1158_;
v___y_1125_ = v_t_x3f_1157_;
v_d_x3f_1126_ = v___x_1193_;
goto v___jp_1122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* v_m_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_stx_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Elab_elabTerminationHints___redArg(v_inst_1216_, v_inst_1217_, v_stx_1218_);
return v___x_1219_;
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
