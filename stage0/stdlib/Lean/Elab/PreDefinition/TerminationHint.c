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
v___x_122_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_122_, 10, v___x_120_);
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
v_options_142_ = lean_ctor_get(v___y_137_, 1);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_161_, uint8_t v___y_162_, lean_object* v_x_163_){
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
return v___x_171_;
}
else
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2));
v___x_173_ = lean_string_dec_eq(v_str_166_, v___x_172_);
if (v___x_173_ == 0)
{
return v___x_173_;
}
else
{
return v_suppressElabErrors_161_;
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
return v___x_175_;
}
else
{
return v_suppressElabErrors_161_;
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
return v___x_181_;
}
else
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5));
v___x_183_ = lean_string_dec_eq(v_str_178_, v___x_182_);
if (v___x_183_ == 0)
{
return v___x_183_;
}
else
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6));
v___x_185_ = lean_string_dec_eq(v_str_177_, v___x_184_);
if (v___x_185_ == 0)
{
return v___x_185_;
}
else
{
return v_suppressElabErrors_161_;
}
}
}
}
else
{
return v___y_162_;
}
}
default: 
{
return v___y_162_;
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
return v___x_188_;
}
else
{
return v_suppressElabErrors_161_;
}
}
default: 
{
return v___y_162_;
}
}
}
else
{
return v___y_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_189_, lean_object* v___y_190_, lean_object* v_x_191_){
_start:
{
uint8_t v_suppressElabErrors_boxed_192_; uint8_t v___y_3293__boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_suppressElabErrors_boxed_192_ = lean_unbox(v_suppressElabErrors_189_);
v___y_3293__boxed_193_ = lean_unbox(v___y_190_);
v_res_194_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_192_, v___y_3293__boxed_193_, v_x_191_);
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
lean_object* v___y_219_; uint8_t v___y_220_; uint8_t v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_255_; lean_object* v___y_256_; uint8_t v___y_257_; uint8_t v___y_258_; uint8_t v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_281_; lean_object* v___y_282_; uint8_t v___y_283_; uint8_t v___y_284_; uint8_t v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_291_; lean_object* v___y_292_; uint8_t v___y_293_; uint8_t v___y_294_; lean_object* v___y_295_; uint8_t v___y_296_; uint8_t v___x_301_; lean_object* v___y_303_; uint8_t v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; uint8_t v___y_307_; uint8_t v___y_308_; uint8_t v___y_310_; uint8_t v___x_324_; 
v___x_301_ = 2;
v___x_324_ = l_Lean_instBEqMessageSeverity_beq(v_severity_213_, v___x_301_);
if (v___x_324_ == 0)
{
v___y_310_ = v___x_324_;
goto v___jp_309_;
}
else
{
uint8_t v___x_325_; 
lean_inc_ref(v_msgData_212_);
v___x_325_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_212_);
v___y_310_ = v___x_325_;
goto v___jp_309_;
}
v___jp_218_:
{
lean_object* v___x_228_; lean_object* v_currNamespace_229_; lean_object* v_openDecls_230_; lean_object* v_env_231_; lean_object* v_nextMacroScope_232_; lean_object* v_ngen_233_; lean_object* v_auxDeclNGen_234_; lean_object* v_traceState_235_; lean_object* v_cache_236_; lean_object* v_messages_237_; lean_object* v_infoState_238_; lean_object* v_snapshotTasks_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_253_; 
v___x_228_ = lean_st_ref_take(v___y_227_);
v_currNamespace_229_ = lean_ctor_get(v___y_226_, 5);
v_openDecls_230_ = lean_ctor_get(v___y_226_, 6);
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
lean_ctor_set(v___x_244_, 1, v___y_222_);
lean_inc_ref(v___y_225_);
lean_inc_ref(v___y_219_);
v___x_245_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_245_, 0, v___y_219_);
lean_ctor_set(v___x_245_, 1, v___y_224_);
lean_ctor_set(v___x_245_, 2, v___y_223_);
lean_ctor_set(v___x_245_, 3, v___y_225_);
lean_ctor_set(v___x_245_, 4, v___x_244_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5, v___y_221_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5 + 1, v___y_220_);
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
v___x_249_ = lean_st_ref_put(v___y_227_, v___x_248_);
v___x_250_ = lean_box(0);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
}
v___jp_254_:
{
lean_object* v_fileName_262_; lean_object* v_fileMap_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_279_; 
v_fileName_262_ = lean_ctor_get(v___y_256_, 0);
v_fileMap_263_ = lean_ctor_get(v___y_256_, 1);
v___x_264_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_212_);
v___x_265_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v___x_264_, v___y_215_, v___y_216_);
v_a_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_279_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_279_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_279_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
lean_inc_ref_n(v_fileMap_263_, 2);
v___x_270_ = l_Lean_FileMap_toPosition(v_fileMap_263_, v___y_260_);
lean_dec(v___y_260_);
v___x_271_ = l_Lean_FileMap_toPosition(v_fileMap_263_, v___y_261_);
lean_dec(v___y_261_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
v___x_273_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0));
if (v___y_257_ == 0)
{
lean_del_object(v___x_268_);
lean_dec_ref(v___y_255_);
v___y_219_ = v_fileName_262_;
v___y_220_ = v___y_258_;
v___y_221_ = v___y_259_;
v___y_222_ = v_a_266_;
v___y_223_ = v___x_272_;
v___y_224_ = v___x_270_;
v___y_225_ = v___x_273_;
v___y_226_ = v___y_215_;
v___y_227_ = v___y_216_;
goto v___jp_218_;
}
else
{
uint8_t v___x_274_; 
lean_inc(v_a_266_);
v___x_274_ = l_Lean_MessageData_hasTag(v___y_255_, v_a_266_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_277_; 
lean_dec_ref_known(v___x_272_, 1);
lean_dec_ref(v___x_270_);
lean_dec(v_a_266_);
v___x_275_ = lean_box(0);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_275_);
v___x_277_ = v___x_268_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
else
{
lean_del_object(v___x_268_);
v___y_219_ = v_fileName_262_;
v___y_220_ = v___y_258_;
v___y_221_ = v___y_259_;
v___y_222_ = v_a_266_;
v___y_223_ = v___x_272_;
v___y_224_ = v___x_270_;
v___y_225_ = v___x_273_;
v___y_226_ = v___y_215_;
v___y_227_ = v___y_216_;
goto v___jp_218_;
}
}
}
}
v___jp_280_:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Syntax_getTailPos_x3f(v___y_286_, v___y_285_);
lean_dec(v___y_286_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_inc(v___y_287_);
v___y_255_ = v___y_281_;
v___y_256_ = v___y_282_;
v___y_257_ = v___y_284_;
v___y_258_ = v___y_283_;
v___y_259_ = v___y_285_;
v___y_260_ = v___y_287_;
v___y_261_ = v___y_287_;
goto v___jp_254_;
}
else
{
lean_object* v_val_289_; 
v_val_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_val_289_);
lean_dec_ref_known(v___x_288_, 1);
v___y_255_ = v___y_281_;
v___y_256_ = v___y_282_;
v___y_257_ = v___y_284_;
v___y_258_ = v___y_283_;
v___y_259_ = v___y_285_;
v___y_260_ = v___y_287_;
v___y_261_ = v_val_289_;
goto v___jp_254_;
}
}
v___jp_290_:
{
lean_object* v_ref_297_; lean_object* v___x_298_; 
v_ref_297_ = l_Lean_replaceRef(v_ref_211_, v___y_295_);
v___x_298_ = l_Lean_Syntax_getPos_x3f(v_ref_297_, v___y_294_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___y_281_ = v___y_291_;
v___y_282_ = v___y_292_;
v___y_283_ = v___y_296_;
v___y_284_ = v___y_293_;
v___y_285_ = v___y_294_;
v___y_286_ = v_ref_297_;
v___y_287_ = v___x_299_;
goto v___jp_280_;
}
else
{
lean_object* v_val_300_; 
v_val_300_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_val_300_);
lean_dec_ref_known(v___x_298_, 1);
v___y_281_ = v___y_291_;
v___y_282_ = v___y_292_;
v___y_283_ = v___y_296_;
v___y_284_ = v___y_293_;
v___y_285_ = v___y_294_;
v___y_286_ = v_ref_297_;
v___y_287_ = v_val_300_;
goto v___jp_280_;
}
}
v___jp_302_:
{
if (v___y_308_ == 0)
{
v___y_291_ = v___y_305_;
v___y_292_ = v___y_303_;
v___y_293_ = v___y_304_;
v___y_294_ = v___y_307_;
v___y_295_ = v___y_306_;
v___y_296_ = v_severity_213_;
goto v___jp_290_;
}
else
{
v___y_291_ = v___y_305_;
v___y_292_ = v___y_303_;
v___y_293_ = v___y_304_;
v___y_294_ = v___y_307_;
v___y_295_ = v___y_306_;
v___y_296_ = v___x_301_;
goto v___jp_290_;
}
}
v___jp_309_:
{
if (v___y_310_ == 0)
{
lean_object* v_toCold_311_; lean_object* v_options_312_; lean_object* v_ref_313_; uint8_t v_suppressElabErrors_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___f_317_; uint8_t v___x_318_; uint8_t v___x_319_; 
v_toCold_311_ = lean_ctor_get(v___y_215_, 0);
v_options_312_ = lean_ctor_get(v___y_215_, 1);
v_ref_313_ = lean_ctor_get(v___y_215_, 4);
v_suppressElabErrors_314_ = lean_ctor_get_uint8(v___y_215_, sizeof(void*)*10 + 1);
v___x_315_ = lean_box(v_suppressElabErrors_314_);
v___x_316_ = lean_box(v___y_310_);
v___f_317_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_317_, 0, v___x_315_);
lean_closure_set(v___f_317_, 1, v___x_316_);
v___x_318_ = 1;
v___x_319_ = l_Lean_instBEqMessageSeverity_beq(v_severity_213_, v___x_318_);
if (v___x_319_ == 0)
{
v___y_303_ = v_toCold_311_;
v___y_304_ = v_suppressElabErrors_314_;
v___y_305_ = v___f_317_;
v___y_306_ = v_ref_313_;
v___y_307_ = v___y_310_;
v___y_308_ = v___x_319_;
goto v___jp_302_;
}
else
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = l_Lean_warningAsError;
v___x_321_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_options_312_, v___x_320_);
v___y_303_ = v_toCold_311_;
v___y_304_ = v_suppressElabErrors_314_;
v___y_305_ = v___f_317_;
v___y_306_ = v_ref_313_;
v___y_307_ = v___y_310_;
v___y_308_ = v___x_321_;
goto v___jp_302_;
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref(v_msgData_212_);
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
lean_object* v_ref_376_; lean_object* v_terminationBy_x3f_x3f_377_; lean_object* v_terminationBy_x3f_378_; lean_object* v_partialFixpoint_x3f_379_; lean_object* v_decreasingBy_x3f_380_; lean_object* v___y_382_; lean_object* v___y_383_; 
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
lean_dec_ref(v_hints_371_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_377_) == 0)
{
if (lean_obj_tag(v_terminationBy_x3f_378_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_380_) == 0)
{
lean_dec(v_ref_376_);
if (lean_obj_tag(v_partialFixpoint_x3f_379_) == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec_ref(v_reason_372_);
v___x_388_ = lean_box(0);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
else
{
lean_object* v_val_390_; uint8_t v_fixpointType_391_; 
v_val_390_ = lean_ctor_get(v_partialFixpoint_x3f_379_, 0);
lean_inc(v_val_390_);
lean_dec_ref_known(v_partialFixpoint_x3f_379_, 1);
v_fixpointType_391_ = lean_ctor_get_uint8(v_val_390_, sizeof(void*)*2);
switch(v_fixpointType_391_)
{
case 0:
{
lean_object* v_ref_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_ref_392_ = lean_ctor_get(v_val_390_, 0);
lean_inc(v_ref_392_);
lean_dec(v_val_390_);
v___x_393_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__3, &l_Lean_Elab_TerminationHints_ensureNone___closed__3_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3);
v___x_394_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_392_, v___x_395_, v_a_373_, v_a_374_);
lean_dec(v_ref_392_);
return v___x_396_;
}
case 1:
{
lean_object* v_ref_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_ref_397_ = lean_ctor_get(v_val_390_, 0);
lean_inc(v_ref_397_);
lean_dec(v_val_390_);
v___x_398_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__5, &l_Lean_Elab_TerminationHints_ensureNone___closed__5_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5);
v___x_399_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_397_, v___x_400_, v_a_373_, v_a_374_);
lean_dec(v_ref_397_);
return v___x_401_;
}
default: 
{
lean_object* v_ref_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_ref_402_ = lean_ctor_get(v_val_390_, 0);
lean_inc(v_ref_402_);
lean_dec(v_val_390_);
v___x_403_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__7, &l_Lean_Elab_TerminationHints_ensureNone___closed__7_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7);
v___x_404_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_402_, v___x_405_, v_a_373_, v_a_374_);
lean_dec(v_ref_402_);
return v___x_406_;
}
}
}
}
else
{
if (lean_obj_tag(v_partialFixpoint_x3f_379_) == 0)
{
lean_object* v_val_407_; lean_object* v_ref_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_ref_376_);
v_val_407_ = lean_ctor_get(v_decreasingBy_x3f_380_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v_decreasingBy_x3f_380_, 1);
v_ref_408_ = lean_ctor_get(v_val_407_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v_val_407_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v_val_407_, 1);
lean_dec(v_unused_419_);
v___x_410_ = v_val_407_;
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_ref_408_);
lean_dec(v_val_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_412_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__9, &l_Lean_Elab_TerminationHints_ensureNone___closed__9_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9);
v___x_413_ = l_Lean_stringToMessageData(v_reason_372_);
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 7);
lean_ctor_set(v___x_410_, 1, v___x_413_);
lean_ctor_set(v___x_410_, 0, v___x_412_);
v___x_415_ = v___x_410_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_413_);
v___x_415_ = v_reuseFailAlloc_417_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_408_, v___x_415_, v_a_373_, v_a_374_);
lean_dec(v_ref_408_);
return v___x_416_;
}
}
}
else
{
lean_dec_ref_known(v_decreasingBy_x3f_380_, 1);
lean_dec(v_partialFixpoint_x3f_379_);
v___y_382_ = v_a_373_;
v___y_383_ = v_a_374_;
goto v___jp_381_;
}
}
}
else
{
if (lean_obj_tag(v_decreasingBy_x3f_380_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_379_) == 0)
{
lean_object* v_val_420_; lean_object* v_ref_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v_ref_376_);
v_val_420_ = lean_ctor_get(v_terminationBy_x3f_378_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v_terminationBy_x3f_378_, 1);
v_ref_421_ = lean_ctor_get(v_val_420_, 0);
lean_inc(v_ref_421_);
lean_dec(v_val_420_);
v___x_422_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__11, &l_Lean_Elab_TerminationHints_ensureNone___closed__11_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11);
v___x_423_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_421_, v___x_424_, v_a_373_, v_a_374_);
lean_dec(v_ref_421_);
return v___x_425_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_378_, 1);
lean_dec(v_partialFixpoint_x3f_379_);
v___y_382_ = v_a_373_;
v___y_383_ = v_a_374_;
goto v___jp_381_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_378_, 1);
lean_dec(v_decreasingBy_x3f_380_);
lean_dec(v_partialFixpoint_x3f_379_);
v___y_382_ = v_a_373_;
v___y_383_ = v_a_374_;
goto v___jp_381_;
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
lean_object* v_val_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_ref_376_);
v_val_426_ = lean_ctor_get(v_terminationBy_x3f_x3f_377_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_377_, 1);
v___x_427_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__13, &l_Lean_Elab_TerminationHints_ensureNone___closed__13_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13);
v___x_428_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_val_426_, v___x_429_, v_a_373_, v_a_374_);
lean_dec(v_val_426_);
return v___x_430_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_377_, 1);
lean_dec(v_partialFixpoint_x3f_379_);
v___y_382_ = v_a_373_;
v___y_383_ = v_a_374_;
goto v___jp_381_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_377_, 1);
lean_dec(v_decreasingBy_x3f_380_);
lean_dec(v_partialFixpoint_x3f_379_);
v___y_382_ = v_a_373_;
v___y_383_ = v_a_374_;
goto v___jp_381_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_377_, 1);
lean_dec(v_decreasingBy_x3f_380_);
lean_dec(v_partialFixpoint_x3f_379_);
lean_dec(v_terminationBy_x3f_378_);
v___y_382_ = v_a_373_;
v___y_383_ = v_a_374_;
goto v___jp_381_;
}
}
v___jp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__1, &l_Lean_Elab_TerminationHints_ensureNone___closed__1_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1);
v___x_385_ = l_Lean_stringToMessageData(v_reason_372_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_376_, v___x_386_, v___y_382_, v___y_383_);
lean_dec(v_ref_376_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone___boxed(lean_object* v_hints_431_, lean_object* v_reason_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Elab_TerminationHints_ensureNone(v_hints_431_, v_reason_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
return v_res_436_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_TerminationHints_isNotNone(lean_object* v_hints_437_){
_start:
{
lean_object* v_terminationBy_x3f_x3f_438_; 
v_terminationBy_x3f_x3f_438_ = lean_ctor_get(v_hints_437_, 1);
if (lean_obj_tag(v_terminationBy_x3f_x3f_438_) == 0)
{
lean_object* v_terminationBy_x3f_439_; 
v_terminationBy_x3f_439_ = lean_ctor_get(v_hints_437_, 2);
if (lean_obj_tag(v_terminationBy_x3f_439_) == 0)
{
lean_object* v_decreasingBy_x3f_440_; 
v_decreasingBy_x3f_440_ = lean_ctor_get(v_hints_437_, 4);
if (lean_obj_tag(v_decreasingBy_x3f_440_) == 0)
{
lean_object* v_partialFixpoint_x3f_441_; 
v_partialFixpoint_x3f_441_ = lean_ctor_get(v_hints_437_, 3);
if (lean_obj_tag(v_partialFixpoint_x3f_441_) == 0)
{
uint8_t v___x_442_; 
v___x_442_ = 0;
return v___x_442_;
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
else
{
uint8_t v___x_445_; 
v___x_445_ = 1;
return v___x_445_;
}
}
else
{
uint8_t v___x_446_; 
v___x_446_ = 1;
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_isNotNone___boxed(lean_object* v_hints_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l_Lean_Elab_TerminationHints_isNotNone(v_hints_447_);
lean_dec_ref(v_hints_447_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object* v_headerParams_450_, lean_object* v_hints_451_, lean_object* v_value_452_){
_start:
{
lean_object* v_ref_453_; lean_object* v_terminationBy_x3f_x3f_454_; lean_object* v_terminationBy_x3f_455_; lean_object* v_partialFixpoint_x3f_456_; lean_object* v_decreasingBy_x3f_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_466_; 
v_ref_453_ = lean_ctor_get(v_hints_451_, 0);
v_terminationBy_x3f_x3f_454_ = lean_ctor_get(v_hints_451_, 1);
v_terminationBy_x3f_455_ = lean_ctor_get(v_hints_451_, 2);
v_partialFixpoint_x3f_456_ = lean_ctor_get(v_hints_451_, 3);
v_decreasingBy_x3f_457_ = lean_ctor_get(v_hints_451_, 4);
v_isSharedCheck_466_ = !lean_is_exclusive(v_hints_451_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v_hints_451_, 5);
lean_dec(v_unused_467_);
v___x_459_ = v_hints_451_;
v_isShared_460_ = v_isSharedCheck_466_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_decreasingBy_x3f_457_);
lean_inc(v_partialFixpoint_x3f_456_);
lean_inc(v_terminationBy_x3f_455_);
lean_inc(v_terminationBy_x3f_x3f_454_);
lean_inc(v_ref_453_);
lean_dec(v_hints_451_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_466_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_461_ = l_Lean_Expr_getNumHeadLambdas(v_value_452_);
v___x_462_ = lean_nat_sub(v___x_461_, v_headerParams_450_);
lean_dec(v___x_461_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 5, v___x_462_);
v___x_464_ = v___x_459_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_ref_453_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_terminationBy_x3f_x3f_454_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_terminationBy_x3f_455_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_partialFixpoint_x3f_456_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_decreasingBy_x3f_457_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(lean_object* v_headerParams_468_, lean_object* v_hints_469_, lean_object* v_value_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v_headerParams_468_, v_hints_469_, v_value_470_);
lean_dec_ref(v_value_470_);
lean_dec(v_headerParams_468_);
return v_res_471_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3));
v___x_479_ = l_Lean_MessageData_ofFormat(v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(lean_object* v_a_480_){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_nat_dec_eq(v_a_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_483_ = l_Nat_reprFast(v_a_480_);
v___x_484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
v___x_485_ = l_Lean_MessageData_ofFormat(v___x_484_);
v___x_486_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; 
lean_dec(v_a_480_);
v___x_488_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4, &l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(lean_object* v_msgData_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; lean_object* v_env_496_; lean_object* v___x_497_; lean_object* v_mctx_498_; lean_object* v_lctx_499_; lean_object* v_options_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_495_ = lean_st_ref_get(v___y_493_);
v_env_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref(v_env_496_);
lean_dec(v___x_495_);
v___x_497_ = lean_st_ref_get(v___y_491_);
v_mctx_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc_ref(v_mctx_498_);
lean_dec(v___x_497_);
v_lctx_499_ = lean_ctor_get(v___y_490_, 2);
v_options_500_ = lean_ctor_get(v___y_492_, 1);
lean_inc_ref(v_options_500_);
lean_inc_ref(v_lctx_499_);
v___x_501_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_501_, 0, v_env_496_);
lean_ctor_set(v___x_501_, 1, v_mctx_498_);
lean_ctor_set(v___x_501_, 2, v_lctx_499_);
lean_ctor_set(v___x_501_, 3, v_options_500_);
v___x_502_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v_msgData_489_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_ref_517_; lean_object* v___x_518_; lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_527_; 
v_ref_517_ = lean_ctor_get(v___y_514_, 4);
v___x_518_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msg_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_527_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
lean_inc(v_ref_517_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_ref_517_);
lean_ctor_set(v___x_523_, 1, v_a_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 1);
lean_ctor_set(v___x_521_, 0, v___x_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_msg_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object* v_ref_535_, lean_object* v_msg_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_toCold_542_; lean_object* v_options_543_; lean_object* v_currRecDepth_544_; lean_object* v_maxRecDepth_545_; lean_object* v_ref_546_; lean_object* v_currNamespace_547_; lean_object* v_openDecls_548_; lean_object* v_initHeartbeats_549_; lean_object* v_maxHeartbeats_550_; lean_object* v_currMacroScope_551_; uint8_t v_diag_552_; uint8_t v_suppressElabErrors_553_; lean_object* v_ref_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_toCold_542_ = lean_ctor_get(v___y_539_, 0);
v_options_543_ = lean_ctor_get(v___y_539_, 1);
v_currRecDepth_544_ = lean_ctor_get(v___y_539_, 2);
v_maxRecDepth_545_ = lean_ctor_get(v___y_539_, 3);
v_ref_546_ = lean_ctor_get(v___y_539_, 4);
v_currNamespace_547_ = lean_ctor_get(v___y_539_, 5);
v_openDecls_548_ = lean_ctor_get(v___y_539_, 6);
v_initHeartbeats_549_ = lean_ctor_get(v___y_539_, 7);
v_maxHeartbeats_550_ = lean_ctor_get(v___y_539_, 8);
v_currMacroScope_551_ = lean_ctor_get(v___y_539_, 9);
v_diag_552_ = lean_ctor_get_uint8(v___y_539_, sizeof(void*)*10);
v_suppressElabErrors_553_ = lean_ctor_get_uint8(v___y_539_, sizeof(void*)*10 + 1);
v_ref_554_ = l_Lean_replaceRef(v_ref_535_, v_ref_546_);
lean_inc(v_currMacroScope_551_);
lean_inc(v_maxHeartbeats_550_);
lean_inc(v_initHeartbeats_549_);
lean_inc(v_openDecls_548_);
lean_inc(v_currNamespace_547_);
lean_inc(v_maxRecDepth_545_);
lean_inc(v_currRecDepth_544_);
lean_inc_ref(v_options_543_);
lean_inc_ref(v_toCold_542_);
v___x_555_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_555_, 0, v_toCold_542_);
lean_ctor_set(v___x_555_, 1, v_options_543_);
lean_ctor_set(v___x_555_, 2, v_currRecDepth_544_);
lean_ctor_set(v___x_555_, 3, v_maxRecDepth_545_);
lean_ctor_set(v___x_555_, 4, v_ref_554_);
lean_ctor_set(v___x_555_, 5, v_currNamespace_547_);
lean_ctor_set(v___x_555_, 6, v_openDecls_548_);
lean_ctor_set(v___x_555_, 7, v_initHeartbeats_549_);
lean_ctor_set(v___x_555_, 8, v_maxHeartbeats_550_);
lean_ctor_set(v___x_555_, 9, v_currMacroScope_551_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*10, v_diag_552_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*10 + 1, v_suppressElabErrors_553_);
v___x_556_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_536_, v___y_537_, v___y_538_, v___x_555_, v___y_540_);
lean_dec_ref_known(v___x_555_, 10);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object* v_ref_557_, lean_object* v_msg_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_557_, v_msg_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v_ref_557_);
return v_res_564_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__1(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__0));
v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__3(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__2));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__5(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__4));
v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__9(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__8));
v___x_579_ = l_Lean_stringToMessageData(v___x_578_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationBy_checkVars___closed__12(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__11));
v___x_584_ = l_Lean_MessageData_ofFormat(v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object* v_funName_585_, lean_object* v_extraParams_586_, lean_object* v_tb_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
uint8_t v_synthetic_593_; 
v_synthetic_593_ = lean_ctor_get_uint8(v_tb_587_, sizeof(void*)*3 + 1);
if (v_synthetic_593_ == 0)
{
lean_object* v_ref_594_; lean_object* v_vars_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_ref_594_ = lean_ctor_get(v_tb_587_, 0);
v_vars_595_ = lean_ctor_get(v_tb_587_, 1);
v___x_596_ = lean_array_get_size(v_vars_595_);
v___x_597_ = lean_nat_dec_lt(v_extraParams_586_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_extraParams_586_);
lean_dec(v_funName_585_);
v___x_598_ = lean_box(0);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v_msg_610_; lean_object* v___x_611_; lean_object* v_ident_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_600_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_596_);
v___x_601_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__1, &l_Lean_Elab_TerminationBy_checkVars___closed__1_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__1);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
lean_inc(v_funName_585_);
v___x_603_ = l_Lean_MessageData_ofName(v_funName_585_);
v___x_604_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__3, &l_Lean_Elab_TerminationBy_checkVars___closed__3_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__3);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_586_);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__5, &l_Lean_Elab_TerminationBy_checkVars___closed__5_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__5);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v_msg_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_610_, 0, v___x_602_);
lean_ctor_set(v_msg_610_, 1, v___x_609_);
v___x_611_ = lean_unsigned_to_nat(0u);
v_ident_612_ = lean_array_fget_borrowed(v_vars_595_, v___x_611_);
v___x_613_ = ((lean_object*)(l_Lean_Elab_TerminationBy_checkVars___closed__7));
lean_inc(v_ident_612_);
v___x_614_ = l_Lean_Syntax_isOfKind(v_ident_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
lean_dec(v_funName_585_);
v___x_615_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_594_, v_msg_610_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = l_Lean_TSyntax_getId(v_ident_612_);
v___x_617_ = l_Lean_Name_isSuffixOf(v___x_616_, v_funName_585_);
lean_dec(v_funName_585_);
lean_dec(v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_594_, v_msg_610_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_msg_622_; lean_object* v___x_623_; 
v___x_619_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__9, &l_Lean_Elab_TerminationBy_checkVars___closed__9_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__9);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v_msg_610_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_obj_once(&l_Lean_Elab_TerminationBy_checkVars___closed__12, &l_Lean_Elab_TerminationBy_checkVars___closed__12_once, _init_l_Lean_Elab_TerminationBy_checkVars___closed__12);
v_msg_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_622_, 0, v___x_620_);
lean_ctor_set(v_msg_622_, 1, v___x_621_);
v___x_623_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_594_, v_msg_622_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
return v___x_623_;
}
}
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v_extraParams_586_);
lean_dec(v_funName_585_);
v___x_624_ = lean_box(0);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object* v_funName_626_, lean_object* v_extraParams_627_, lean_object* v_tb_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Elab_TerminationBy_checkVars(v_funName_626_, v_extraParams_627_, v_tb_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec_ref(v_tb_628_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(lean_object* v_00_u03b1_635_, lean_object* v_ref_636_, lean_object* v_msg_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_636_, v_msg_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object* v_00_u03b1_644_, lean_object* v_ref_645_, lean_object* v_msg_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(v_00_u03b1_644_, v_ref_645_, v_msg_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v_ref_645_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(lean_object* v_00_u03b1_653_, lean_object* v_msg_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_661_, lean_object* v_msg_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_661_, v_msg_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object* v_val_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v_val_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object* v_stx_671_, lean_object* v_terminationBy_x3f_x3f_672_, lean_object* v_terminationBy_x3f_673_, lean_object* v_partialFixpoint_x3f_674_, lean_object* v___x_675_, lean_object* v_toPure_676_, lean_object* v_decreasingBy_x3f_677_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_678_, 0, v_stx_671_);
lean_ctor_set(v___x_678_, 1, v_terminationBy_x3f_x3f_672_);
lean_ctor_set(v___x_678_, 2, v_terminationBy_x3f_673_);
lean_ctor_set(v___x_678_, 3, v_partialFixpoint_x3f_674_);
lean_ctor_set(v___x_678_, 4, v_decreasingBy_x3f_677_);
lean_ctor_set(v___x_678_, 5, v___x_675_);
v___x_679_ = lean_apply_2(v_toPure_676_, lean_box(0), v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* v_stx_684_, lean_object* v_terminationBy_x3f_x3f_685_, lean_object* v_terminationBy_x3f_686_, lean_object* v___x_687_, lean_object* v_toPure_688_, lean_object* v_d_x3f_689_, lean_object* v_toBind_690_, lean_object* v_toFunctor_691_, lean_object* v___f_692_, lean_object* v___x_693_, lean_object* v___x_694_, lean_object* v___x_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v___x_698_, lean_object* v_partialFixpoint_x3f_699_){
_start:
{
lean_object* v___f_700_; 
lean_inc(v_toPure_688_);
v___f_700_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1), 7, 6);
lean_closure_set(v___f_700_, 0, v_stx_684_);
lean_closure_set(v___f_700_, 1, v_terminationBy_x3f_x3f_685_);
lean_closure_set(v___f_700_, 2, v_terminationBy_x3f_686_);
lean_closure_set(v___f_700_, 3, v_partialFixpoint_x3f_699_);
lean_closure_set(v___f_700_, 4, v___x_687_);
lean_closure_set(v___f_700_, 5, v_toPure_688_);
if (lean_obj_tag(v_d_x3f_689_) == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec_ref(v___f_692_);
lean_dec_ref(v_toFunctor_691_);
v___x_701_ = lean_box(0);
v___x_702_ = lean_apply_2(v_toPure_688_, lean_box(0), v___x_701_);
v___x_703_ = lean_apply_4(v_toBind_690_, lean_box(0), lean_box(0), v___x_702_, v___f_700_);
return v___x_703_;
}
else
{
lean_object* v_val_704_; lean_object* v_map_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_723_; 
v_val_704_ = lean_ctor_get(v_d_x3f_689_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v_d_x3f_689_, 1);
v_map_705_ = lean_ctor_get(v_toFunctor_691_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_toFunctor_691_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v_toFunctor_691_, 1);
lean_dec(v_unused_724_);
v___x_707_ = v_toFunctor_691_;
v_isShared_708_ = v_isSharedCheck_723_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_map_705_);
lean_dec(v_toFunctor_691_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_723_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___y_710_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_713_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0));
v___x_714_ = l_Lean_Name_mkStr4(v___x_693_, v___x_694_, v___x_695_, v___x_713_);
lean_inc(v_val_704_);
v___x_715_ = l_Lean_Syntax_isOfKind(v_val_704_, v___x_714_);
lean_dec(v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_del_object(v___x_707_);
lean_dec(v_toPure_688_);
v___x_716_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2, &l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2);
v___x_717_ = l_Lean_throwErrorAt___redArg(v_inst_696_, v_inst_697_, v_val_704_, v___x_716_);
v___y_710_ = v___x_717_;
goto v___jp_709_;
}
else
{
lean_object* v_tactic_718_; lean_object* v___x_720_; 
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
v_tactic_718_ = l_Lean_Syntax_getArg(v_val_704_, v___x_698_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v_tactic_718_);
lean_ctor_set(v___x_707_, 0, v_val_704_);
v___x_720_ = v___x_707_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_val_704_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_tactic_718_);
v___x_720_ = v_reuseFailAlloc_722_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; 
v___x_721_ = lean_apply_2(v_toPure_688_, lean_box(0), v___x_720_);
v___y_710_ = v___x_721_;
goto v___jp_709_;
}
}
v___jp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_apply_4(v_map_705_, lean_box(0), lean_box(0), v___f_692_, v___y_710_);
v___x_712_ = lean_apply_4(v_toBind_690_, lean_box(0), lean_box(0), v___x_711_, v___f_700_);
return v___x_712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object* v_stx_725_, lean_object* v_terminationBy_x3f_x3f_726_, lean_object* v_terminationBy_x3f_727_, lean_object* v___x_728_, lean_object* v_toPure_729_, lean_object* v_d_x3f_730_, lean_object* v_toBind_731_, lean_object* v_toFunctor_732_, lean_object* v___f_733_, lean_object* v___x_734_, lean_object* v___x_735_, lean_object* v___x_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v___x_739_, lean_object* v_partialFixpoint_x3f_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_725_, v_terminationBy_x3f_x3f_726_, v_terminationBy_x3f_727_, v___x_728_, v_toPure_729_, v_d_x3f_730_, v_toBind_731_, v_toFunctor_732_, v___f_733_, v___x_734_, v___x_735_, v___x_736_, v_inst_737_, v_inst_738_, v___x_739_, v_partialFixpoint_x3f_740_);
lean_dec(v___x_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object* v___f_742_, lean_object* v_partialFixpoint_x3f_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_apply_1(v___f_742_, v_partialFixpoint_x3f_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object* v_stx_748_, lean_object* v_terminationBy_x3f_x3f_749_, lean_object* v___x_750_, lean_object* v_toPure_751_, lean_object* v_d_x3f_752_, lean_object* v_toBind_753_, lean_object* v_toFunctor_754_, lean_object* v___f_755_, lean_object* v___x_756_, lean_object* v___x_757_, lean_object* v___x_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v___x_761_, lean_object* v_t_x3f_762_, lean_object* v_terminationBy_x3f_763_){
_start:
{
lean_object* v___f_764_; 
lean_inc(v___x_761_);
lean_inc_ref(v___x_758_);
lean_inc_ref(v___x_757_);
lean_inc_ref(v___x_756_);
lean_inc(v_toBind_753_);
lean_inc(v_toPure_751_);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed), 16, 15);
lean_closure_set(v___f_764_, 0, v_stx_748_);
lean_closure_set(v___f_764_, 1, v_terminationBy_x3f_x3f_749_);
lean_closure_set(v___f_764_, 2, v_terminationBy_x3f_763_);
lean_closure_set(v___f_764_, 3, v___x_750_);
lean_closure_set(v___f_764_, 4, v_toPure_751_);
lean_closure_set(v___f_764_, 5, v_d_x3f_752_);
lean_closure_set(v___f_764_, 6, v_toBind_753_);
lean_closure_set(v___f_764_, 7, v_toFunctor_754_);
lean_closure_set(v___f_764_, 8, v___f_755_);
lean_closure_set(v___f_764_, 9, v___x_756_);
lean_closure_set(v___f_764_, 10, v___x_757_);
lean_closure_set(v___f_764_, 11, v___x_758_);
lean_closure_set(v___f_764_, 12, v_inst_759_);
lean_closure_set(v___f_764_, 13, v_inst_760_);
lean_closure_set(v___f_764_, 14, v___x_761_);
if (lean_obj_tag(v_t_x3f_762_) == 1)
{
lean_object* v_val_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_842_; 
v_val_765_ = lean_ctor_get(v_t_x3f_762_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_t_x3f_762_);
if (v_isSharedCheck_842_ == 0)
{
v___x_767_ = v_t_x3f_762_;
v_isShared_768_ = v_isSharedCheck_842_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_val_765_);
lean_dec(v_t_x3f_762_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_842_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_769_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_758_);
lean_inc_ref(v___x_757_);
lean_inc_ref(v___x_756_);
v___x_770_ = l_Lean_Name_mkStr4(v___x_756_, v___x_757_, v___x_758_, v___x_769_);
lean_inc(v_val_765_);
v___x_771_ = l_Lean_Syntax_isOfKind(v_val_765_, v___x_770_);
lean_dec(v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_758_);
lean_inc_ref(v___x_757_);
lean_inc_ref(v___x_756_);
v___x_773_ = l_Lean_Name_mkStr4(v___x_756_, v___x_757_, v___x_758_, v___x_772_);
lean_inc(v_val_765_);
v___x_774_ = l_Lean_Syntax_isOfKind(v_val_765_, v___x_773_);
lean_dec(v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_775_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_776_ = l_Lean_Name_mkStr4(v___x_756_, v___x_757_, v___x_758_, v___x_775_);
lean_inc(v_val_765_);
v___x_777_ = l_Lean_Syntax_isOfKind(v_val_765_, v___x_776_);
lean_dec(v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_del_object(v___x_767_);
lean_dec(v_val_765_);
lean_dec(v___x_761_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_778_, 0, v___f_764_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_779_);
v___x_781_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_780_, v___f_778_);
return v___x_781_;
}
else
{
lean_object* v___f_782_; lean_object* v_term_x3f_784_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___f_782_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_782_, 0, v___f_764_);
v___x_792_ = l_Lean_Syntax_getArg(v_val_765_, v___x_761_);
v___x_793_ = l_Lean_Syntax_isNone(v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_792_);
v___x_795_ = l_Lean_Syntax_matchesNull(v___x_792_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v___x_792_);
lean_del_object(v___x_767_);
lean_dec(v_val_765_);
lean_dec(v___x_761_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_796_);
v___x_798_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_797_, v___f_782_);
return v___x_798_;
}
else
{
lean_object* v_term_x3f_799_; lean_object* v___x_800_; 
v_term_x3f_799_ = l_Lean_Syntax_getArg(v___x_792_, v___x_761_);
lean_dec(v___x_761_);
lean_dec(v___x_792_);
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v_term_x3f_799_);
v_term_x3f_784_ = v___x_800_;
goto v___jp_783_;
}
}
else
{
lean_object* v___x_801_; 
lean_dec(v___x_792_);
lean_dec(v___x_761_);
v___x_801_ = lean_box(0);
v_term_x3f_784_ = v___x_801_;
goto v___jp_783_;
}
v___jp_783_:
{
uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = 2;
v___x_786_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_786_, 0, v_val_765_);
lean_ctor_set(v___x_786_, 1, v_term_x3f_784_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*2, v___x_785_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_786_);
v___x_788_ = v___x_767_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_791_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_788_);
v___x_790_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_789_, v___f_782_);
return v___x_790_;
}
}
}
}
else
{
lean_object* v___f_802_; lean_object* v_term_x3f_804_; lean_object* v___x_812_; uint8_t v___x_813_; 
lean_dec_ref(v___x_758_);
lean_dec_ref(v___x_757_);
lean_dec_ref(v___x_756_);
v___f_802_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_802_, 0, v___f_764_);
v___x_812_ = l_Lean_Syntax_getArg(v_val_765_, v___x_761_);
v___x_813_ = l_Lean_Syntax_isNone(v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_812_);
v___x_815_ = l_Lean_Syntax_matchesNull(v___x_812_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec(v___x_812_);
lean_del_object(v___x_767_);
lean_dec(v_val_765_);
lean_dec(v___x_761_);
v___x_816_ = lean_box(0);
v___x_817_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_816_);
v___x_818_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_817_, v___f_802_);
return v___x_818_;
}
else
{
lean_object* v_term_x3f_819_; lean_object* v___x_820_; 
v_term_x3f_819_ = l_Lean_Syntax_getArg(v___x_812_, v___x_761_);
lean_dec(v___x_761_);
lean_dec(v___x_812_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v_term_x3f_819_);
v_term_x3f_804_ = v___x_820_;
goto v___jp_803_;
}
}
else
{
lean_object* v___x_821_; 
lean_dec(v___x_812_);
lean_dec(v___x_761_);
v___x_821_ = lean_box(0);
v_term_x3f_804_ = v___x_821_;
goto v___jp_803_;
}
v___jp_803_:
{
uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_805_ = 1;
v___x_806_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_806_, 0, v_val_765_);
lean_ctor_set(v___x_806_, 1, v_term_x3f_804_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*2, v___x_805_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_806_);
v___x_808_ = v___x_767_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_811_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_808_);
v___x_810_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_809_, v___f_802_);
return v___x_810_;
}
}
}
}
else
{
lean_object* v___f_822_; lean_object* v_term_x3f_824_; lean_object* v___x_832_; uint8_t v___x_833_; 
lean_dec_ref(v___x_758_);
lean_dec_ref(v___x_757_);
lean_dec_ref(v___x_756_);
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_822_, 0, v___f_764_);
v___x_832_ = l_Lean_Syntax_getArg(v_val_765_, v___x_761_);
v___x_833_ = l_Lean_Syntax_isNone(v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_832_);
v___x_835_ = l_Lean_Syntax_matchesNull(v___x_832_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v___x_832_);
lean_del_object(v___x_767_);
lean_dec(v_val_765_);
lean_dec(v___x_761_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_836_);
v___x_838_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_837_, v___f_822_);
return v___x_838_;
}
else
{
lean_object* v_term_x3f_839_; lean_object* v___x_840_; 
v_term_x3f_839_ = l_Lean_Syntax_getArg(v___x_832_, v___x_761_);
lean_dec(v___x_761_);
lean_dec(v___x_832_);
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v_term_x3f_839_);
v_term_x3f_824_ = v___x_840_;
goto v___jp_823_;
}
}
else
{
lean_object* v___x_841_; 
lean_dec(v___x_832_);
lean_dec(v___x_761_);
v___x_841_ = lean_box(0);
v_term_x3f_824_ = v___x_841_;
goto v___jp_823_;
}
v___jp_823_:
{
uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_825_ = 0;
v___x_826_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_826_, 0, v_val_765_);
lean_ctor_set(v___x_826_, 1, v_term_x3f_824_);
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*2, v___x_825_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_826_);
v___x_828_ = v___x_767_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_831_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_828_);
v___x_830_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_829_, v___f_822_);
return v___x_830_;
}
}
}
}
}
else
{
lean_object* v___f_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v_t_x3f_762_);
lean_dec(v___x_761_);
lean_dec_ref(v___x_758_);
lean_dec_ref(v___x_757_);
lean_dec_ref(v___x_756_);
v___f_843_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_843_, 0, v___f_764_);
v___x_844_ = lean_box(0);
v___x_845_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_844_);
v___x_846_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_845_, v___f_843_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* v___f_847_, lean_object* v_terminationBy_x3f_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_apply_1(v___f_847_, v_terminationBy_x3f_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2));
v___x_854_ = l_Lean_stringToMessageData(v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4));
v___x_857_ = l_Lean_stringToMessageData(v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* v_stx_858_, lean_object* v___x_859_, lean_object* v_toPure_860_, lean_object* v_d_x3f_861_, lean_object* v_toBind_862_, lean_object* v_toFunctor_863_, lean_object* v___f_864_, lean_object* v___x_865_, lean_object* v___x_866_, lean_object* v___x_867_, lean_object* v_inst_868_, lean_object* v_inst_869_, lean_object* v___x_870_, lean_object* v_t_x3f_871_, lean_object* v_terminationBy_x3f_x3f_872_){
_start:
{
lean_object* v___f_873_; 
lean_inc(v_t_x3f_871_);
lean_inc(v___x_870_);
lean_inc_ref(v_inst_869_);
lean_inc_ref(v_inst_868_);
lean_inc_ref(v___x_867_);
lean_inc_ref(v___x_866_);
lean_inc_ref(v___x_865_);
lean_inc(v_toBind_862_);
lean_inc(v_toPure_860_);
lean_inc(v___x_859_);
v___f_873_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11), 16, 15);
lean_closure_set(v___f_873_, 0, v_stx_858_);
lean_closure_set(v___f_873_, 1, v_terminationBy_x3f_x3f_872_);
lean_closure_set(v___f_873_, 2, v___x_859_);
lean_closure_set(v___f_873_, 3, v_toPure_860_);
lean_closure_set(v___f_873_, 4, v_d_x3f_861_);
lean_closure_set(v___f_873_, 5, v_toBind_862_);
lean_closure_set(v___f_873_, 6, v_toFunctor_863_);
lean_closure_set(v___f_873_, 7, v___f_864_);
lean_closure_set(v___f_873_, 8, v___x_865_);
lean_closure_set(v___f_873_, 9, v___x_866_);
lean_closure_set(v___f_873_, 10, v___x_867_);
lean_closure_set(v___f_873_, 11, v_inst_868_);
lean_closure_set(v___f_873_, 12, v_inst_869_);
lean_closure_set(v___f_873_, 13, v___x_870_);
lean_closure_set(v___f_873_, 14, v_t_x3f_871_);
if (lean_obj_tag(v_t_x3f_871_) == 1)
{
lean_object* v_val_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_986_; 
v_val_874_ = lean_ctor_get(v_t_x3f_871_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v_t_x3f_871_);
if (v_isSharedCheck_986_ == 0)
{
v___x_876_ = v_t_x3f_871_;
v_isShared_877_ = v_isSharedCheck_986_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_val_874_);
lean_dec(v_t_x3f_871_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_986_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_878_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0));
lean_inc_ref(v___x_867_);
lean_inc_ref(v___x_866_);
lean_inc_ref(v___x_865_);
v___x_879_ = l_Lean_Name_mkStr4(v___x_865_, v___x_866_, v___x_867_, v___x_878_);
lean_inc(v_val_874_);
v___x_880_ = l_Lean_Syntax_isOfKind(v_val_874_, v___x_879_);
lean_dec(v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
lean_del_object(v___x_876_);
lean_dec(v___x_859_);
v___x_881_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1));
lean_inc_ref(v___x_867_);
lean_inc_ref(v___x_866_);
lean_inc_ref(v___x_865_);
v___x_882_ = l_Lean_Name_mkStr4(v___x_865_, v___x_866_, v___x_867_, v___x_881_);
lean_inc(v_val_874_);
v___x_883_ = l_Lean_Syntax_isOfKind(v_val_874_, v___x_882_);
lean_dec(v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_884_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_867_);
lean_inc_ref(v___x_866_);
lean_inc_ref(v___x_865_);
v___x_885_ = l_Lean_Name_mkStr4(v___x_865_, v___x_866_, v___x_867_, v___x_884_);
lean_inc(v_val_874_);
v___x_886_ = l_Lean_Syntax_isOfKind(v_val_874_, v___x_885_);
lean_dec(v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_887_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_867_);
lean_inc_ref(v___x_866_);
lean_inc_ref(v___x_865_);
v___x_888_ = l_Lean_Name_mkStr4(v___x_865_, v___x_866_, v___x_867_, v___x_887_);
lean_inc(v_val_874_);
v___x_889_ = l_Lean_Syntax_isOfKind(v_val_874_, v___x_888_);
lean_dec(v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_890_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_891_ = l_Lean_Name_mkStr4(v___x_865_, v___x_866_, v___x_867_, v___x_890_);
lean_inc(v_val_874_);
v___x_892_ = l_Lean_Syntax_isOfKind(v_val_874_, v___x_891_);
lean_dec(v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec(v___x_870_);
lean_dec(v_toPure_860_);
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_893_, 0, v___f_873_);
v___x_894_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_895_ = l_Lean_throwErrorAt___redArg(v_inst_868_, v_inst_869_, v_val_874_, v___x_894_);
v___x_896_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_895_, v___f_893_);
return v___x_896_;
}
else
{
lean_object* v___f_897_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___f_897_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_897_, 0, v___f_873_);
v___x_902_ = l_Lean_Syntax_getArg(v_val_874_, v___x_870_);
lean_dec(v___x_870_);
v___x_903_ = l_Lean_Syntax_isNone(v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(2u);
v___x_905_ = l_Lean_Syntax_matchesNull(v___x_902_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec(v_toPure_860_);
v___x_906_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_907_ = l_Lean_throwErrorAt___redArg(v_inst_868_, v_inst_869_, v_val_874_, v___x_906_);
v___x_908_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_907_, v___f_897_);
return v___x_908_;
}
else
{
lean_dec(v_val_874_);
lean_dec_ref(v_inst_869_);
lean_dec_ref(v_inst_868_);
goto v___jp_898_;
}
}
else
{
lean_dec(v___x_902_);
lean_dec(v_val_874_);
lean_dec_ref(v_inst_869_);
lean_dec_ref(v_inst_868_);
goto v___jp_898_;
}
v___jp_898_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_box(0);
v___x_900_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_899_);
v___x_901_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_900_, v___f_897_);
return v___x_901_;
}
}
}
else
{
lean_object* v___f_909_; lean_object* v___x_914_; uint8_t v___x_915_; 
lean_dec_ref(v___x_867_);
lean_dec_ref(v___x_866_);
lean_dec_ref(v___x_865_);
v___f_909_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_909_, 0, v___f_873_);
v___x_914_ = l_Lean_Syntax_getArg(v_val_874_, v___x_870_);
lean_dec(v___x_870_);
v___x_915_ = l_Lean_Syntax_isNone(v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_unsigned_to_nat(2u);
v___x_917_ = l_Lean_Syntax_matchesNull(v___x_914_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_toPure_860_);
v___x_918_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_919_ = l_Lean_throwErrorAt___redArg(v_inst_868_, v_inst_869_, v_val_874_, v___x_918_);
v___x_920_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_919_, v___f_909_);
return v___x_920_;
}
else
{
lean_dec(v_val_874_);
lean_dec_ref(v_inst_869_);
lean_dec_ref(v_inst_868_);
goto v___jp_910_;
}
}
else
{
lean_dec(v___x_914_);
lean_dec(v_val_874_);
lean_dec_ref(v_inst_869_);
lean_dec_ref(v_inst_868_);
goto v___jp_910_;
}
v___jp_910_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = lean_box(0);
v___x_912_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_911_);
v___x_913_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_912_, v___f_909_);
return v___x_913_;
}
}
}
else
{
lean_object* v___f_921_; lean_object* v___x_926_; uint8_t v___x_927_; 
lean_dec_ref(v___x_867_);
lean_dec_ref(v___x_866_);
lean_dec_ref(v___x_865_);
v___f_921_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_921_, 0, v___f_873_);
v___x_926_ = l_Lean_Syntax_getArg(v_val_874_, v___x_870_);
lean_dec(v___x_870_);
v___x_927_ = l_Lean_Syntax_isNone(v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = lean_unsigned_to_nat(2u);
v___x_929_ = l_Lean_Syntax_matchesNull(v___x_926_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_toPure_860_);
v___x_930_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_931_ = l_Lean_throwErrorAt___redArg(v_inst_868_, v_inst_869_, v_val_874_, v___x_930_);
v___x_932_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_931_, v___f_921_);
return v___x_932_;
}
else
{
lean_dec(v_val_874_);
lean_dec_ref(v_inst_869_);
lean_dec_ref(v_inst_868_);
goto v___jp_922_;
}
}
else
{
lean_dec(v___x_926_);
lean_dec(v_val_874_);
lean_dec_ref(v_inst_869_);
lean_dec_ref(v_inst_868_);
goto v___jp_922_;
}
v___jp_922_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = lean_box(0);
v___x_924_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_923_);
v___x_925_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_924_, v___f_921_);
return v___x_925_;
}
}
}
else
{
lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec(v_val_874_);
lean_dec(v___x_870_);
lean_dec_ref(v_inst_869_);
lean_dec_ref(v_inst_868_);
lean_dec_ref(v___x_867_);
lean_dec_ref(v___x_866_);
lean_dec_ref(v___x_865_);
v___f_933_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_933_, 0, v___f_873_);
v___x_934_ = lean_box(0);
v___x_935_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_934_);
v___x_936_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_935_, v___f_933_);
return v___x_936_;
}
}
else
{
lean_object* v___f_937_; lean_object* v___y_939_; lean_object* v___y_940_; uint8_t v___y_941_; uint8_t v___y_942_; uint8_t v___y_950_; lean_object* v___y_951_; uint8_t v___y_952_; lean_object* v_s_959_; lean_object* v___x_977_; uint8_t v___x_978_; 
lean_dec_ref(v___x_867_);
lean_dec_ref(v___x_866_);
lean_dec_ref(v___x_865_);
v___f_937_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_937_, 0, v___f_873_);
v___x_977_ = l_Lean_Syntax_getArg(v_val_874_, v___x_870_);
v___x_978_ = l_Lean_Syntax_isNone(v___x_977_);
if (v___x_978_ == 0)
{
uint8_t v___x_979_; 
lean_inc(v___x_977_);
v___x_979_ = l_Lean_Syntax_matchesNull(v___x_977_, v___x_870_);
lean_dec(v___x_870_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec(v___x_977_);
lean_del_object(v___x_876_);
lean_dec(v_toPure_860_);
lean_dec(v___x_859_);
v___x_980_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_981_ = l_Lean_throwErrorAt___redArg(v_inst_868_, v_inst_869_, v_val_874_, v___x_980_);
v___x_982_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_981_, v___f_937_);
return v___x_982_;
}
else
{
lean_object* v_s_983_; lean_object* v___x_984_; 
v_s_983_ = l_Lean_Syntax_getArg(v___x_977_, v___x_859_);
lean_dec(v___x_977_);
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v_s_983_);
v_s_959_ = v___x_984_;
goto v___jp_958_;
}
}
else
{
lean_object* v___x_985_; 
lean_dec(v___x_977_);
lean_dec(v___x_870_);
v___x_985_ = lean_box(0);
v_s_959_ = v___x_985_;
goto v___jp_958_;
}
v___jp_938_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_943_, 0, v_val_874_);
lean_ctor_set(v___x_943_, 1, v___y_940_);
lean_ctor_set(v___x_943_, 2, v___y_939_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*3, v___y_942_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*3 + 1, v___y_941_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_943_);
v___x_945_ = v___x_876_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_948_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_945_);
v___x_947_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_946_, v___f_937_);
return v___x_947_;
}
}
v___jp_949_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_953_ = lean_mk_empty_array_with_capacity(v___x_859_);
lean_dec(v___x_859_);
v___x_954_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_954_, 0, v_val_874_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
lean_ctor_set(v___x_954_, 2, v___y_951_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*3, v___y_952_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*3 + 1, v___y_950_);
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
v___x_956_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_955_);
v___x_957_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_956_, v___f_937_);
return v___x_957_;
}
v___jp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_960_ = lean_unsigned_to_nat(2u);
v___x_961_ = l_Lean_Syntax_getArg(v_val_874_, v___x_960_);
lean_inc(v___x_961_);
v___x_962_ = l_Lean_Syntax_matchesNull(v___x_961_, v___x_960_);
if (v___x_962_ == 0)
{
uint8_t v___x_963_; 
lean_del_object(v___x_876_);
v___x_963_ = l_Lean_Syntax_matchesNull(v___x_961_, v___x_859_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v_s_959_);
lean_dec(v_toPure_860_);
lean_dec(v___x_859_);
v___x_964_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_965_ = l_Lean_throwErrorAt___redArg(v_inst_868_, v_inst_869_, v_val_874_, v___x_964_);
v___x_966_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_965_, v___f_937_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v_body_968_; 
lean_dec_ref(v_inst_869_);
lean_dec_ref(v_inst_868_);
v___x_967_ = lean_unsigned_to_nat(3u);
v_body_968_ = l_Lean_Syntax_getArg(v_val_874_, v___x_967_);
if (lean_obj_tag(v_s_959_) == 0)
{
v___y_950_ = v___x_962_;
v___y_951_ = v_body_968_;
v___y_952_ = v___x_962_;
goto v___jp_949_;
}
else
{
lean_dec_ref_known(v_s_959_, 1);
v___y_950_ = v___x_962_;
v___y_951_ = v_body_968_;
v___y_952_ = v___x_963_;
goto v___jp_949_;
}
}
}
else
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = l_Lean_Syntax_getArg(v___x_961_, v___x_859_);
lean_dec(v___x_961_);
lean_inc(v___x_969_);
v___x_970_ = l_Lean_Syntax_matchesNull(v___x_969_, v___x_859_);
lean_dec(v___x_859_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v_body_972_; lean_object* v_vars_973_; 
lean_dec_ref(v_inst_869_);
lean_dec_ref(v_inst_868_);
v___x_971_ = lean_unsigned_to_nat(3u);
v_body_972_ = l_Lean_Syntax_getArg(v_val_874_, v___x_971_);
v_vars_973_ = l_Lean_Syntax_getArgs(v___x_969_);
lean_dec(v___x_969_);
if (lean_obj_tag(v_s_959_) == 0)
{
v___y_939_ = v_body_972_;
v___y_940_ = v_vars_973_;
v___y_941_ = v___x_970_;
v___y_942_ = v___x_970_;
goto v___jp_938_;
}
else
{
lean_dec_ref_known(v_s_959_, 1);
v___y_939_ = v_body_972_;
v___y_940_ = v_vars_973_;
v___y_941_ = v___x_970_;
v___y_942_ = v___x_962_;
goto v___jp_938_;
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec(v___x_969_);
lean_dec(v_s_959_);
lean_del_object(v___x_876_);
lean_dec(v_toPure_860_);
v___x_974_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
v___x_975_ = l_Lean_throwErrorAt___redArg(v_inst_868_, v_inst_869_, v_val_874_, v___x_974_);
v___x_976_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_975_, v___f_937_);
return v___x_976_;
}
}
}
}
}
}
else
{
lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v_t_x3f_871_);
lean_dec(v___x_870_);
lean_dec_ref(v_inst_869_);
lean_dec_ref(v_inst_868_);
lean_dec_ref(v___x_867_);
lean_dec_ref(v___x_866_);
lean_dec_ref(v___x_865_);
lean_dec(v___x_859_);
v___f_987_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_987_, 0, v___f_873_);
v___x_988_ = lean_box(0);
v___x_989_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_988_);
v___x_990_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_989_, v___f_987_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* v___f_991_, lean_object* v_terminationBy_x3f_x3f_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = lean_apply_1(v___f_991_, v_terminationBy_x3f_x3f_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_stx_1018_){
_start:
{
if (lean_obj_tag(v_stx_1018_) == 0)
{
lean_object* v_toApplicative_1019_; lean_object* v_toPure_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_toApplicative_1019_ = lean_ctor_get(v_inst_1016_, 0);
lean_inc_ref(v_toApplicative_1019_);
lean_dec_ref(v_inst_1017_);
lean_dec_ref(v_inst_1016_);
v_toPure_1020_ = lean_ctor_get(v_toApplicative_1019_, 1);
lean_inc(v_toPure_1020_);
lean_dec_ref(v_toApplicative_1019_);
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = lean_box(0);
v___x_1023_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1023_, 0, v_stx_1018_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
lean_ctor_set(v___x_1023_, 2, v___x_1022_);
lean_ctor_set(v___x_1023_, 3, v___x_1022_);
lean_ctor_set(v___x_1023_, 4, v___x_1022_);
lean_ctor_set(v___x_1023_, 5, v___x_1021_);
v___x_1024_ = lean_apply_2(v_toPure_1020_, lean_box(0), v___x_1023_);
return v___x_1024_;
}
else
{
lean_object* v_toApplicative_1025_; lean_object* v_toBind_1026_; lean_object* v_toFunctor_1027_; lean_object* v_toPure_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_toApplicative_1025_ = lean_ctor_get(v_inst_1016_, 0);
v_toBind_1026_ = lean_ctor_get(v_inst_1016_, 1);
v_toFunctor_1027_ = lean_ctor_get(v_toApplicative_1025_, 0);
v_toPure_1028_ = lean_ctor_get(v_toApplicative_1025_, 1);
v___x_1029_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__0));
v___x_1030_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__1));
v___x_1031_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__2));
v___x_1032_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__4));
lean_inc(v_stx_1018_);
v___x_1033_ = l_Lean_Syntax_isOfKind(v_stx_1018_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1034_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1035_ = lean_box(0);
lean_inc_n(v_stx_1018_, 2);
v___x_1036_ = l_Lean_Syntax_formatStx(v_stx_1018_, v___x_1035_, v___x_1033_);
v___x_1037_ = l_Std_Format_defWidth;
v___x_1038_ = lean_unsigned_to_nat(0u);
v___x_1039_ = l_Std_Format_pretty(v___x_1036_, v___x_1037_, v___x_1038_, v___x_1038_);
v___x_1040_ = lean_string_append(v___x_1034_, v___x_1039_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1042_ = lean_string_append(v___x_1040_, v___x_1041_);
v___x_1043_ = l_Lean_Syntax_getKind(v_stx_1018_);
v___x_1044_ = 1;
v___x_1045_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1043_, v___x_1044_);
v___x_1046_ = lean_string_append(v___x_1042_, v___x_1045_);
lean_dec_ref(v___x_1045_);
v___x_1047_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
v___x_1048_ = l_Lean_MessageData_ofFormat(v___x_1047_);
v___x_1049_ = l_Lean_throwErrorAt___redArg(v_inst_1016_, v_inst_1017_, v_stx_1018_, v___x_1048_);
return v___x_1049_;
}
else
{
lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v_d_x3f_1056_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v_t_x3f_1086_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___f_1050_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__7));
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1123_ = l_Lean_Syntax_getArg(v_stx_1018_, v___x_1051_);
v___x_1124_ = l_Lean_Syntax_isNone(v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1123_);
v___x_1126_ = l_Lean_Syntax_matchesNull(v___x_1123_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec(v___x_1123_);
v___x_1127_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1128_ = lean_box(0);
lean_inc_n(v_stx_1018_, 2);
v___x_1129_ = l_Lean_Syntax_formatStx(v_stx_1018_, v___x_1128_, v___x_1126_);
v___x_1130_ = l_Std_Format_defWidth;
v___x_1131_ = l_Std_Format_pretty(v___x_1129_, v___x_1130_, v___x_1051_, v___x_1051_);
v___x_1132_ = lean_string_append(v___x_1127_, v___x_1131_);
lean_dec_ref(v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1134_ = lean_string_append(v___x_1132_, v___x_1133_);
v___x_1135_ = l_Lean_Syntax_getKind(v_stx_1018_);
v___x_1136_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1135_, v___x_1033_);
v___x_1137_ = lean_string_append(v___x_1134_, v___x_1136_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
v___x_1139_ = l_Lean_MessageData_ofFormat(v___x_1138_);
v___x_1140_ = l_Lean_throwErrorAt___redArg(v_inst_1016_, v_inst_1017_, v_stx_1018_, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v_t_x3f_1141_; lean_object* v___x_1142_; 
v_t_x3f_1141_ = l_Lean_Syntax_getArg(v___x_1123_, v___x_1051_);
lean_dec(v___x_1123_);
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_t_x3f_1141_);
v_t_x3f_1086_ = v___x_1142_;
goto v___jp_1085_;
}
}
else
{
lean_object* v___x_1143_; 
lean_dec(v___x_1123_);
v___x_1143_ = lean_box(0);
v_t_x3f_1086_ = v___x_1143_;
goto v___jp_1085_;
}
v___jp_1052_:
{
lean_object* v___f_1057_; 
lean_inc(v_toBind_1026_);
lean_inc(v_toPure_1028_);
v___f_1057_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19), 15, 14);
lean_closure_set(v___f_1057_, 0, v_stx_1018_);
lean_closure_set(v___f_1057_, 1, v___x_1051_);
lean_closure_set(v___f_1057_, 2, v_toPure_1028_);
lean_closure_set(v___f_1057_, 3, v_d_x3f_1056_);
lean_closure_set(v___f_1057_, 4, v_toBind_1026_);
lean_closure_set(v___f_1057_, 5, v_toFunctor_1027_);
lean_closure_set(v___f_1057_, 6, v___f_1050_);
lean_closure_set(v___f_1057_, 7, v___x_1029_);
lean_closure_set(v___f_1057_, 8, v___x_1030_);
lean_closure_set(v___f_1057_, 9, v___x_1031_);
lean_closure_set(v___f_1057_, 10, v_inst_1016_);
lean_closure_set(v___f_1057_, 11, v_inst_1017_);
lean_closure_set(v___f_1057_, 12, v___y_1054_);
lean_closure_set(v___f_1057_, 13, v___y_1053_);
if (lean_obj_tag(v___y_1055_) == 1)
{
lean_object* v_val_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1074_; 
v_val_1058_ = lean_ctor_get(v___y_1055_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___y_1055_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1060_ = v___y_1055_;
v_isShared_1061_ = v_isSharedCheck_1074_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_val_1058_);
lean_dec(v___y_1055_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1074_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__8));
lean_inc(v_val_1058_);
v___x_1063_ = l_Lean_Syntax_isOfKind(v_val_1058_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_del_object(v___x_1060_);
lean_dec(v_val_1058_);
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1064_, 0, v___f_1057_);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_apply_2(v_toPure_1028_, lean_box(0), v___x_1065_);
v___x_1067_ = lean_apply_4(v_toBind_1026_, lean_box(0), lean_box(0), v___x_1066_, v___f_1064_);
return v___x_1067_;
}
else
{
lean_object* v___f_1068_; lean_object* v___x_1070_; 
v___f_1068_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1068_, 0, v___f_1057_);
if (v_isShared_1061_ == 0)
{
v___x_1070_ = v___x_1060_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_val_1058_);
v___x_1070_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_apply_2(v_toPure_1028_, lean_box(0), v___x_1070_);
v___x_1072_ = lean_apply_4(v_toBind_1026_, lean_box(0), lean_box(0), v___x_1071_, v___f_1068_);
return v___x_1072_;
}
}
}
}
else
{
lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec(v___y_1055_);
v___f_1075_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1075_, 0, v___f_1057_);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_apply_2(v_toPure_1028_, lean_box(0), v___x_1076_);
v___x_1078_ = lean_apply_4(v_toBind_1026_, lean_box(0), lean_box(0), v___x_1077_, v___f_1075_);
return v___x_1078_;
}
}
v___jp_1079_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___y_1083_);
v___y_1053_ = v___y_1080_;
v___y_1054_ = v___y_1081_;
v___y_1055_ = v___y_1082_;
v_d_x3f_1056_ = v___x_1084_;
goto v___jp_1052_;
}
v___jp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = lean_unsigned_to_nat(1u);
v___x_1088_ = l_Lean_Syntax_getArg(v_stx_1018_, v___x_1087_);
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
lean_inc_n(v_stx_1018_, 2);
v___x_1093_ = l_Lean_Syntax_formatStx(v_stx_1018_, v___x_1092_, v___x_1090_);
v___x_1094_ = l_Std_Format_defWidth;
v___x_1095_ = l_Std_Format_pretty(v___x_1093_, v___x_1094_, v___x_1051_, v___x_1051_);
v___x_1096_ = lean_string_append(v___x_1091_, v___x_1095_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1098_ = lean_string_append(v___x_1096_, v___x_1097_);
v___x_1099_ = l_Lean_Syntax_getKind(v_stx_1018_);
v___x_1100_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1099_, v___x_1033_);
v___x_1101_ = lean_string_append(v___x_1098_, v___x_1100_);
lean_dec_ref(v___x_1100_);
v___x_1102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
v___x_1103_ = l_Lean_MessageData_ofFormat(v___x_1102_);
v___x_1104_ = l_Lean_throwErrorAt___redArg(v_inst_1016_, v_inst_1017_, v_stx_1018_, v___x_1103_);
return v___x_1104_;
}
else
{
lean_object* v_d_x3f_1105_; 
v_d_x3f_1105_ = l_Lean_Syntax_getArg(v___x_1088_, v___x_1051_);
lean_dec(v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
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
lean_inc_n(v_stx_1018_, 2);
v___x_1110_ = l_Lean_Syntax_formatStx(v_stx_1018_, v___x_1109_, v___x_1089_);
v___x_1111_ = l_Std_Format_defWidth;
v___x_1112_ = l_Std_Format_pretty(v___x_1110_, v___x_1111_, v___x_1051_, v___x_1051_);
v___x_1113_ = lean_string_append(v___x_1108_, v___x_1112_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1115_ = lean_string_append(v___x_1113_, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_getKind(v_stx_1018_);
v___x_1117_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1116_, v___x_1090_);
v___x_1118_ = lean_string_append(v___x_1115_, v___x_1117_);
lean_dec_ref(v___x_1117_);
v___x_1119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
v___x_1120_ = l_Lean_MessageData_ofFormat(v___x_1119_);
v___x_1121_ = l_Lean_throwErrorAt___redArg(v_inst_1016_, v_inst_1017_, v_stx_1018_, v___x_1120_);
return v___x_1121_;
}
else
{
lean_inc(v_toPure_1028_);
lean_inc_ref(v_toFunctor_1027_);
lean_inc(v_toBind_1026_);
lean_inc(v_t_x3f_1086_);
v___y_1080_ = v_t_x3f_1086_;
v___y_1081_ = v___x_1087_;
v___y_1082_ = v_t_x3f_1086_;
v___y_1083_ = v_d_x3f_1105_;
goto v___jp_1079_;
}
}
else
{
lean_inc(v_toPure_1028_);
lean_inc_ref(v_toFunctor_1027_);
lean_inc(v_toBind_1026_);
lean_inc(v_t_x3f_1086_);
v___y_1080_ = v_t_x3f_1086_;
v___y_1081_ = v___x_1087_;
v___y_1082_ = v_t_x3f_1086_;
v___y_1083_ = v_d_x3f_1105_;
goto v___jp_1079_;
}
}
}
else
{
lean_object* v___x_1122_; 
lean_inc(v_toPure_1028_);
lean_inc_ref(v_toFunctor_1027_);
lean_inc(v_toBind_1026_);
lean_dec(v___x_1088_);
v___x_1122_ = lean_box(0);
lean_inc(v_t_x3f_1086_);
v___y_1053_ = v_t_x3f_1086_;
v___y_1054_ = v___x_1087_;
v___y_1055_ = v_t_x3f_1086_;
v_d_x3f_1056_ = v___x_1122_;
goto v___jp_1052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* v_m_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_stx_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Elab_elabTerminationHints___redArg(v_inst_1145_, v_inst_1146_, v_stx_1147_);
return v___x_1148_;
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
