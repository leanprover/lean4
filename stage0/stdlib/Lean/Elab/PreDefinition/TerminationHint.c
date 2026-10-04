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
lean_object* v___x_140_; lean_object* v_toCold_141_; lean_object* v_env_142_; lean_object* v_options_143_; uint8_t v___x_144_; lean_object* v_env_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_140_ = lean_st_ref_get(v___y_138_);
v_toCold_141_ = lean_ctor_get(v___y_137_, 0);
v_env_142_ = lean_ctor_get(v___x_140_, 0);
lean_inc_ref(v_env_142_);
lean_dec(v___x_140_);
v_options_143_ = lean_ctor_get(v_toCold_141_, 2);
v___x_144_ = 0;
v_env_145_ = l_Lean_Environment_setRecordingDeps(v_env_142_, v___x_144_);
v___x_146_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2);
v___x_147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_143_);
v___x_148_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_148_, 0, v_env_145_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
lean_ctor_set(v___x_148_, 2, v___x_147_);
lean_ctor_set(v___x_148_, 3, v_options_143_);
v___x_149_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_msgData_136_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v_msgData_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_155_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_164_, uint8_t v___y_165_, lean_object* v_x_166_){
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
return v_suppressElabErrors_164_;
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
return v_suppressElabErrors_164_;
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
return v_suppressElabErrors_164_;
}
}
}
}
else
{
return v___y_165_;
}
}
default: 
{
return v___y_165_;
}
}
}
case 0:
{
lean_object* v_str_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_str_189_ = lean_ctor_get(v_x_166_, 1);
v___x_190_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7));
v___x_191_ = lean_string_dec_eq(v_str_189_, v___x_190_);
if (v___x_191_ == 0)
{
return v___x_191_;
}
else
{
return v_suppressElabErrors_164_;
}
}
default: 
{
return v___y_165_;
}
}
}
else
{
return v___y_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_192_, lean_object* v___y_193_, lean_object* v_x_194_){
_start:
{
uint8_t v_suppressElabErrors_boxed_195_; uint8_t v___y_3397__boxed_196_; uint8_t v_res_197_; lean_object* v_r_198_; 
v_suppressElabErrors_boxed_195_ = lean_unbox(v_suppressElabErrors_192_);
v___y_3397__boxed_196_ = lean_unbox(v___y_193_);
v_res_197_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_195_, v___y_3397__boxed_196_, v_x_194_);
lean_dec(v_x_194_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(lean_object* v_opts_199_, lean_object* v_opt_200_){
_start:
{
lean_object* v_name_201_; lean_object* v_defValue_202_; lean_object* v_map_203_; lean_object* v___x_204_; 
v_name_201_ = lean_ctor_get(v_opt_200_, 0);
v_defValue_202_ = lean_ctor_get(v_opt_200_, 1);
v_map_203_ = lean_ctor_get(v_opts_199_, 0);
v___x_204_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_203_, v_name_201_);
if (lean_obj_tag(v___x_204_) == 0)
{
uint8_t v___x_205_; 
v___x_205_ = lean_unbox(v_defValue_202_);
return v___x_205_;
}
else
{
lean_object* v_val_206_; 
v_val_206_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_val_206_);
lean_dec_ref_known(v___x_204_, 1);
if (lean_obj_tag(v_val_206_) == 1)
{
uint8_t v_v_207_; 
v_v_207_ = lean_ctor_get_uint8(v_val_206_, 0);
lean_dec_ref_known(v_val_206_, 0);
return v_v_207_;
}
else
{
uint8_t v___x_208_; 
lean_dec(v_val_206_);
v___x_208_ = lean_unbox(v_defValue_202_);
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_209_, lean_object* v_opt_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_opts_209_, v_opt_210_);
lean_dec_ref(v_opt_210_);
lean_dec_ref(v_opts_209_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(lean_object* v_ref_214_, lean_object* v_msgData_215_, uint8_t v_severity_216_, uint8_t v_isSilent_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
uint8_t v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; uint8_t v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v_toCold_229_; lean_object* v___y_230_; lean_object* v___y_259_; lean_object* v___y_260_; uint8_t v___y_261_; uint8_t v___y_262_; lean_object* v___y_263_; uint8_t v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_286_; lean_object* v___y_287_; uint8_t v___y_288_; uint8_t v___y_289_; uint8_t v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; uint8_t v___y_296_; uint8_t v___y_297_; uint8_t v___y_298_; uint8_t v___x_309_; uint8_t v___y_311_; uint8_t v___y_312_; uint8_t v___y_313_; uint8_t v___y_315_; uint8_t v___x_323_; 
v___x_309_ = 2;
v___x_323_ = l_Lean_instBEqMessageSeverity_beq(v_severity_216_, v___x_309_);
if (v___x_323_ == 0)
{
v___y_315_ = v___x_323_;
goto v___jp_314_;
}
else
{
uint8_t v___x_324_; 
lean_inc_ref(v_msgData_215_);
v___x_324_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_215_);
v___y_315_ = v___x_324_;
goto v___jp_314_;
}
v___jp_221_:
{
lean_object* v_currNamespace_231_; lean_object* v_openDecls_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_env_237_; lean_object* v_nextMacroScope_238_; lean_object* v_ngen_239_; lean_object* v_auxDeclNGen_240_; lean_object* v_traceState_241_; lean_object* v_cache_242_; lean_object* v_recordedDeps_243_; lean_object* v_messages_244_; lean_object* v_infoState_245_; lean_object* v_snapshotTasks_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_257_; 
v_currNamespace_231_ = lean_ctor_get(v_toCold_229_, 4);
v_openDecls_232_ = lean_ctor_get(v_toCold_229_, 5);
lean_inc(v_openDecls_232_);
lean_inc(v_currNamespace_231_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v_currNamespace_231_);
lean_ctor_set(v___x_233_, 1, v_openDecls_232_);
v___x_234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___y_227_);
lean_inc_ref(v___y_228_);
lean_inc_ref(v___y_226_);
v___x_235_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_235_, 0, v___y_226_);
lean_ctor_set(v___x_235_, 1, v___y_223_);
lean_ctor_set(v___x_235_, 2, v___y_224_);
lean_ctor_set(v___x_235_, 3, v___y_228_);
lean_ctor_set(v___x_235_, 4, v___x_234_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*5, v___y_225_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*5 + 1, v___y_222_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*5 + 2, v_isSilent_217_);
v___x_236_ = lean_st_ref_take(v___y_230_);
v_env_237_ = lean_ctor_get(v___x_236_, 0);
v_nextMacroScope_238_ = lean_ctor_get(v___x_236_, 1);
v_ngen_239_ = lean_ctor_get(v___x_236_, 2);
v_auxDeclNGen_240_ = lean_ctor_get(v___x_236_, 3);
v_traceState_241_ = lean_ctor_get(v___x_236_, 4);
v_cache_242_ = lean_ctor_get(v___x_236_, 5);
v_recordedDeps_243_ = lean_ctor_get(v___x_236_, 6);
v_messages_244_ = lean_ctor_get(v___x_236_, 7);
v_infoState_245_ = lean_ctor_get(v___x_236_, 8);
v_snapshotTasks_246_ = lean_ctor_get(v___x_236_, 9);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_257_ == 0)
{
v___x_248_ = v___x_236_;
v_isShared_249_ = v_isSharedCheck_257_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_snapshotTasks_246_);
lean_inc(v_infoState_245_);
lean_inc(v_messages_244_);
lean_inc(v_recordedDeps_243_);
lean_inc(v_cache_242_);
lean_inc(v_traceState_241_);
lean_inc(v_auxDeclNGen_240_);
lean_inc(v_ngen_239_);
lean_inc(v_nextMacroScope_238_);
lean_inc(v_env_237_);
lean_dec(v___x_236_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_257_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_250_ = lean_box(0);
v___x_251_ = l_Lean_MessageLog_add(v___x_235_, v_messages_244_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 7, v___x_251_);
v___x_253_ = v___x_248_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_env_237_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_nextMacroScope_238_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_ngen_239_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_auxDeclNGen_240_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_traceState_241_);
lean_ctor_set(v_reuseFailAlloc_256_, 5, v_cache_242_);
lean_ctor_set(v_reuseFailAlloc_256_, 6, v_recordedDeps_243_);
lean_ctor_set(v_reuseFailAlloc_256_, 7, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_256_, 8, v_infoState_245_);
lean_ctor_set(v_reuseFailAlloc_256_, 9, v_snapshotTasks_246_);
v___x_253_ = v_reuseFailAlloc_256_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_st_ref_put(v___y_230_, v___x_253_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_250_);
return v___x_255_;
}
}
}
v___jp_258_:
{
lean_object* v_fileName_267_; lean_object* v_fileMap_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_284_; 
v_fileName_267_ = lean_ctor_get(v___y_265_, 0);
v_fileMap_268_ = lean_ctor_get(v___y_265_, 1);
v___x_269_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_215_);
v___x_270_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v___x_269_, v___y_218_, v___y_219_);
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_284_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_284_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_284_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
lean_inc_ref_n(v_fileMap_268_, 2);
v___x_275_ = l_Lean_FileMap_toPosition(v_fileMap_268_, v___y_263_);
lean_dec(v___y_263_);
v___x_276_ = l_Lean_FileMap_toPosition(v_fileMap_268_, v___y_266_);
lean_dec(v___y_266_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
v___x_278_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0));
if (v___y_264_ == 0)
{
lean_del_object(v___x_273_);
lean_dec_ref(v___y_259_);
v___y_222_ = v___y_261_;
v___y_223_ = v___x_275_;
v___y_224_ = v___x_277_;
v___y_225_ = v___y_262_;
v___y_226_ = v_fileName_267_;
v___y_227_ = v_a_271_;
v___y_228_ = v___x_278_;
v_toCold_229_ = v___y_260_;
v___y_230_ = v___y_219_;
goto v___jp_221_;
}
else
{
uint8_t v___x_279_; 
lean_inc(v_a_271_);
v___x_279_ = l_Lean_MessageData_hasTag(v___y_259_, v_a_271_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_282_; 
lean_dec_ref_known(v___x_277_, 1);
lean_dec_ref(v___x_275_);
lean_dec(v_a_271_);
v___x_280_ = lean_box(0);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_280_);
v___x_282_ = v___x_273_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
else
{
lean_del_object(v___x_273_);
v___y_222_ = v___y_261_;
v___y_223_ = v___x_275_;
v___y_224_ = v___x_277_;
v___y_225_ = v___y_262_;
v___y_226_ = v_fileName_267_;
v___y_227_ = v_a_271_;
v___y_228_ = v___x_278_;
v_toCold_229_ = v___y_260_;
v___y_230_ = v___y_219_;
goto v___jp_221_;
}
}
}
}
v___jp_285_:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Syntax_getTailPos_x3f(v___y_291_, v___y_290_);
lean_dec(v___y_291_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_inc(v___y_292_);
v___y_259_ = v___y_286_;
v___y_260_ = v___y_287_;
v___y_261_ = v___y_289_;
v___y_262_ = v___y_290_;
v___y_263_ = v___y_292_;
v___y_264_ = v___y_288_;
v___y_265_ = v___y_287_;
v___y_266_ = v___y_292_;
goto v___jp_258_;
}
else
{
lean_object* v_val_294_; 
v_val_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_val_294_);
lean_dec_ref_known(v___x_293_, 1);
v___y_259_ = v___y_286_;
v___y_260_ = v___y_287_;
v___y_261_ = v___y_289_;
v___y_262_ = v___y_290_;
v___y_263_ = v___y_292_;
v___y_264_ = v___y_288_;
v___y_265_ = v___y_287_;
v___y_266_ = v_val_294_;
goto v___jp_258_;
}
}
v___jp_295_:
{
lean_object* v_toCold_299_; lean_object* v_ref_300_; uint8_t v_suppressElabErrors_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___f_304_; lean_object* v_ref_305_; lean_object* v___x_306_; 
v_toCold_299_ = lean_ctor_get(v___y_218_, 0);
v_ref_300_ = lean_ctor_get(v___y_218_, 2);
v_suppressElabErrors_301_ = lean_ctor_get_uint8(v___y_218_, sizeof(void*)*3 + 2);
v___x_302_ = lean_box(v_suppressElabErrors_301_);
v___x_303_ = lean_box(v___y_296_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_304_, 0, v___x_302_);
lean_closure_set(v___f_304_, 1, v___x_303_);
v_ref_305_ = l_Lean_replaceRef(v_ref_214_, v_ref_300_);
v___x_306_ = l_Lean_Syntax_getPos_x3f(v_ref_305_, v___y_297_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___y_286_ = v___f_304_;
v___y_287_ = v_toCold_299_;
v___y_288_ = v_suppressElabErrors_301_;
v___y_289_ = v___y_298_;
v___y_290_ = v___y_297_;
v___y_291_ = v_ref_305_;
v___y_292_ = v___x_307_;
goto v___jp_285_;
}
else
{
lean_object* v_val_308_; 
v_val_308_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v___x_306_, 1);
v___y_286_ = v___f_304_;
v___y_287_ = v_toCold_299_;
v___y_288_ = v_suppressElabErrors_301_;
v___y_289_ = v___y_298_;
v___y_290_ = v___y_297_;
v___y_291_ = v_ref_305_;
v___y_292_ = v_val_308_;
goto v___jp_285_;
}
}
v___jp_310_:
{
if (v___y_313_ == 0)
{
v___y_296_ = v___y_311_;
v___y_297_ = v___y_312_;
v___y_298_ = v_severity_216_;
goto v___jp_295_;
}
else
{
v___y_296_ = v___y_311_;
v___y_297_ = v___y_312_;
v___y_298_ = v___x_309_;
goto v___jp_295_;
}
}
v___jp_314_:
{
if (v___y_315_ == 0)
{
uint8_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 1;
v___x_317_ = l_Lean_instBEqMessageSeverity_beq(v_severity_216_, v___x_316_);
if (v___x_317_ == 0)
{
v___y_311_ = v___y_315_;
v___y_312_ = v___y_315_;
v___y_313_ = v___x_317_;
goto v___jp_310_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_318_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_218_);
v___x_319_ = l_Lean_warningAsError;
v___x_320_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v___x_318_, v___x_319_);
lean_dec_ref(v___x_318_);
v___y_311_ = v___y_315_;
v___y_312_ = v___y_315_;
v___y_313_ = v___x_320_;
goto v___jp_310_;
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref(v_msgData_215_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___boxed(lean_object* v_ref_325_, lean_object* v_msgData_326_, lean_object* v_severity_327_, lean_object* v_isSilent_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
uint8_t v_severity_boxed_332_; uint8_t v_isSilent_boxed_333_; lean_object* v_res_334_; 
v_severity_boxed_332_ = lean_unbox(v_severity_327_);
v_isSilent_boxed_333_ = lean_unbox(v_isSilent_328_);
v_res_334_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_325_, v_msgData_326_, v_severity_boxed_332_, v_isSilent_boxed_333_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v_ref_325_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(lean_object* v_ref_335_, lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
uint8_t v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; 
v___x_340_ = 1;
v___x_341_ = 0;
v___x_342_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_335_, v_msgData_336_, v___x_340_, v___x_341_, v___y_337_, v___y_338_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(lean_object* v_ref_343_, lean_object* v_msgData_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_343_, v_msgData_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v_ref_343_);
return v_res_348_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__0));
v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__2));
v___x_354_ = l_Lean_stringToMessageData(v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__4));
v___x_357_ = l_Lean_stringToMessageData(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__6));
v___x_360_ = l_Lean_stringToMessageData(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__8));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__10));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Elab_TerminationHints_ensureNone___closed__12));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone(lean_object* v_hints_370_, lean_object* v_reason_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_ref_375_; lean_object* v_terminationBy_x3f_x3f_376_; lean_object* v_terminationBy_x3f_377_; lean_object* v_partialFixpoint_x3f_378_; lean_object* v_decreasingBy_x3f_379_; uint8_t v_warnIfRedundant_380_; lean_object* v___y_382_; lean_object* v___y_383_; 
v_ref_375_ = lean_ctor_get(v_hints_370_, 0);
lean_inc(v_ref_375_);
v_terminationBy_x3f_x3f_376_ = lean_ctor_get(v_hints_370_, 1);
lean_inc(v_terminationBy_x3f_x3f_376_);
v_terminationBy_x3f_377_ = lean_ctor_get(v_hints_370_, 2);
lean_inc(v_terminationBy_x3f_377_);
v_partialFixpoint_x3f_378_ = lean_ctor_get(v_hints_370_, 3);
lean_inc(v_partialFixpoint_x3f_378_);
v_decreasingBy_x3f_379_ = lean_ctor_get(v_hints_370_, 4);
lean_inc(v_decreasingBy_x3f_379_);
v_warnIfRedundant_380_ = lean_ctor_get_uint8(v_hints_370_, sizeof(void*)*6);
lean_dec_ref(v_hints_370_);
if (v_warnIfRedundant_380_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec(v_decreasingBy_x3f_379_);
lean_dec(v_partialFixpoint_x3f_378_);
lean_dec(v_terminationBy_x3f_377_);
lean_dec(v_terminationBy_x3f_x3f_376_);
lean_dec(v_ref_375_);
lean_dec_ref(v_reason_371_);
v___x_388_ = lean_box(0);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_x3f_376_) == 0)
{
if (lean_obj_tag(v_terminationBy_x3f_377_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_379_) == 0)
{
lean_dec(v_ref_375_);
if (lean_obj_tag(v_partialFixpoint_x3f_378_) == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec_ref(v_reason_371_);
v___x_390_ = lean_box(0);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
else
{
lean_object* v_val_392_; uint8_t v_fixpointType_393_; 
v_val_392_ = lean_ctor_get(v_partialFixpoint_x3f_378_, 0);
lean_inc(v_val_392_);
lean_dec_ref_known(v_partialFixpoint_x3f_378_, 1);
v_fixpointType_393_ = lean_ctor_get_uint8(v_val_392_, sizeof(void*)*2);
switch(v_fixpointType_393_)
{
case 0:
{
lean_object* v_ref_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_ref_394_ = lean_ctor_get(v_val_392_, 0);
lean_inc(v_ref_394_);
lean_dec(v_val_392_);
v___x_395_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__3, &l_Lean_Elab_TerminationHints_ensureNone___closed__3_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3);
v___x_396_ = l_Lean_stringToMessageData(v_reason_371_);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_394_, v___x_397_, v_a_372_, v_a_373_);
lean_dec(v_ref_394_);
return v___x_398_;
}
case 1:
{
lean_object* v_ref_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_ref_399_ = lean_ctor_get(v_val_392_, 0);
lean_inc(v_ref_399_);
lean_dec(v_val_392_);
v___x_400_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__5, &l_Lean_Elab_TerminationHints_ensureNone___closed__5_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5);
v___x_401_ = l_Lean_stringToMessageData(v_reason_371_);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_399_, v___x_402_, v_a_372_, v_a_373_);
lean_dec(v_ref_399_);
return v___x_403_;
}
default: 
{
lean_object* v_ref_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_ref_404_ = lean_ctor_get(v_val_392_, 0);
lean_inc(v_ref_404_);
lean_dec(v_val_392_);
v___x_405_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__7, &l_Lean_Elab_TerminationHints_ensureNone___closed__7_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7);
v___x_406_ = l_Lean_stringToMessageData(v_reason_371_);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_404_, v___x_407_, v_a_372_, v_a_373_);
lean_dec(v_ref_404_);
return v___x_408_;
}
}
}
}
else
{
if (lean_obj_tag(v_partialFixpoint_x3f_378_) == 0)
{
lean_object* v_val_409_; lean_object* v_ref_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_ref_375_);
v_val_409_ = lean_ctor_get(v_decreasingBy_x3f_379_, 0);
lean_inc(v_val_409_);
lean_dec_ref_known(v_decreasingBy_x3f_379_, 1);
v_ref_410_ = lean_ctor_get(v_val_409_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_val_409_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v_val_409_, 1);
lean_dec(v_unused_421_);
v___x_412_ = v_val_409_;
v_isShared_413_ = v_isSharedCheck_420_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_ref_410_);
lean_dec(v_val_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_420_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_414_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__9, &l_Lean_Elab_TerminationHints_ensureNone___closed__9_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9);
v___x_415_ = l_Lean_stringToMessageData(v_reason_371_);
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 7);
lean_ctor_set(v___x_412_, 1, v___x_415_);
lean_ctor_set(v___x_412_, 0, v___x_414_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v___x_415_);
v___x_417_ = v_reuseFailAlloc_419_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_410_, v___x_417_, v_a_372_, v_a_373_);
lean_dec(v_ref_410_);
return v___x_418_;
}
}
}
else
{
lean_dec_ref_known(v_decreasingBy_x3f_379_, 1);
lean_dec(v_partialFixpoint_x3f_378_);
v___y_382_ = v_a_372_;
v___y_383_ = v_a_373_;
goto v___jp_381_;
}
}
}
else
{
if (lean_obj_tag(v_decreasingBy_x3f_379_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_378_) == 0)
{
lean_object* v_val_422_; lean_object* v_ref_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v_ref_375_);
v_val_422_ = lean_ctor_get(v_terminationBy_x3f_377_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v_terminationBy_x3f_377_, 1);
v_ref_423_ = lean_ctor_get(v_val_422_, 0);
lean_inc(v_ref_423_);
lean_dec(v_val_422_);
v___x_424_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__11, &l_Lean_Elab_TerminationHints_ensureNone___closed__11_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11);
v___x_425_ = l_Lean_stringToMessageData(v_reason_371_);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_423_, v___x_426_, v_a_372_, v_a_373_);
lean_dec(v_ref_423_);
return v___x_427_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_377_, 1);
lean_dec(v_partialFixpoint_x3f_378_);
v___y_382_ = v_a_372_;
v___y_383_ = v_a_373_;
goto v___jp_381_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_377_, 1);
lean_dec(v_decreasingBy_x3f_379_);
lean_dec(v_partialFixpoint_x3f_378_);
v___y_382_ = v_a_372_;
v___y_383_ = v_a_373_;
goto v___jp_381_;
}
}
}
else
{
if (lean_obj_tag(v_terminationBy_x3f_377_) == 0)
{
if (lean_obj_tag(v_decreasingBy_x3f_379_) == 0)
{
if (lean_obj_tag(v_partialFixpoint_x3f_378_) == 0)
{
lean_object* v_val_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec(v_ref_375_);
v_val_428_ = lean_ctor_get(v_terminationBy_x3f_x3f_376_, 0);
lean_inc(v_val_428_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_376_, 1);
v___x_429_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__13, &l_Lean_Elab_TerminationHints_ensureNone___closed__13_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13);
v___x_430_ = l_Lean_stringToMessageData(v_reason_371_);
v___x_431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_val_428_, v___x_431_, v_a_372_, v_a_373_);
lean_dec(v_val_428_);
return v___x_432_;
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_376_, 1);
lean_dec(v_partialFixpoint_x3f_378_);
v___y_382_ = v_a_372_;
v___y_383_ = v_a_373_;
goto v___jp_381_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_376_, 1);
lean_dec(v_decreasingBy_x3f_379_);
lean_dec(v_partialFixpoint_x3f_378_);
v___y_382_ = v_a_372_;
v___y_383_ = v_a_373_;
goto v___jp_381_;
}
}
else
{
lean_dec_ref_known(v_terminationBy_x3f_x3f_376_, 1);
lean_dec(v_decreasingBy_x3f_379_);
lean_dec(v_partialFixpoint_x3f_378_);
lean_dec(v_terminationBy_x3f_377_);
v___y_382_ = v_a_372_;
v___y_383_ = v_a_373_;
goto v___jp_381_;
}
}
}
v___jp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_obj_once(&l_Lean_Elab_TerminationHints_ensureNone___closed__1, &l_Lean_Elab_TerminationHints_ensureNone___closed__1_once, _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1);
v___x_385_ = l_Lean_stringToMessageData(v_reason_371_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_375_, v___x_386_, v___y_382_, v___y_383_);
lean_dec(v_ref_375_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone___boxed(lean_object* v_hints_433_, lean_object* v_reason_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Elab_TerminationHints_ensureNone(v_hints_433_, v_reason_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_438_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_TerminationHints_isNotNone(lean_object* v_hints_439_){
_start:
{
lean_object* v_terminationBy_x3f_x3f_440_; 
v_terminationBy_x3f_x3f_440_ = lean_ctor_get(v_hints_439_, 1);
if (lean_obj_tag(v_terminationBy_x3f_x3f_440_) == 0)
{
lean_object* v_terminationBy_x3f_441_; 
v_terminationBy_x3f_441_ = lean_ctor_get(v_hints_439_, 2);
if (lean_obj_tag(v_terminationBy_x3f_441_) == 0)
{
lean_object* v_decreasingBy_x3f_442_; 
v_decreasingBy_x3f_442_ = lean_ctor_get(v_hints_439_, 4);
if (lean_obj_tag(v_decreasingBy_x3f_442_) == 0)
{
lean_object* v_partialFixpoint_x3f_443_; 
v_partialFixpoint_x3f_443_ = lean_ctor_get(v_hints_439_, 3);
if (lean_obj_tag(v_partialFixpoint_x3f_443_) == 0)
{
uint8_t v___x_444_; 
v___x_444_ = 0;
return v___x_444_;
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_isNotNone___boxed(lean_object* v_hints_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_Lean_Elab_TerminationHints_isNotNone(v_hints_449_);
lean_dec_ref(v_hints_449_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object* v_headerParams_452_, lean_object* v_hints_453_, lean_object* v_value_454_){
_start:
{
lean_object* v_ref_455_; lean_object* v_terminationBy_x3f_x3f_456_; lean_object* v_terminationBy_x3f_457_; lean_object* v_partialFixpoint_x3f_458_; lean_object* v_decreasingBy_x3f_459_; uint8_t v_warnIfRedundant_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_469_; 
v_ref_455_ = lean_ctor_get(v_hints_453_, 0);
v_terminationBy_x3f_x3f_456_ = lean_ctor_get(v_hints_453_, 1);
v_terminationBy_x3f_457_ = lean_ctor_get(v_hints_453_, 2);
v_partialFixpoint_x3f_458_ = lean_ctor_get(v_hints_453_, 3);
v_decreasingBy_x3f_459_ = lean_ctor_get(v_hints_453_, 4);
v_warnIfRedundant_460_ = lean_ctor_get_uint8(v_hints_453_, sizeof(void*)*6);
v_isSharedCheck_469_ = !lean_is_exclusive(v_hints_453_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v_hints_453_, 5);
lean_dec(v_unused_470_);
v___x_462_ = v_hints_453_;
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_decreasingBy_x3f_459_);
lean_inc(v_partialFixpoint_x3f_458_);
lean_inc(v_terminationBy_x3f_457_);
lean_inc(v_terminationBy_x3f_x3f_456_);
lean_inc(v_ref_455_);
lean_dec(v_hints_453_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = l_Lean_Expr_getNumHeadLambdas(v_value_454_);
v___x_465_ = lean_nat_sub(v___x_464_, v_headerParams_452_);
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
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_ref_455_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_terminationBy_x3f_x3f_456_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_terminationBy_x3f_457_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_partialFixpoint_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_decreasingBy_x3f_459_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v___x_465_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, sizeof(void*)*6, v_warnIfRedundant_460_);
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
lean_object* v___x_498_; lean_object* v_env_499_; uint8_t v___x_500_; lean_object* v_env_501_; lean_object* v___x_502_; lean_object* v_toCold_503_; lean_object* v_mctx_504_; lean_object* v_lctx_505_; lean_object* v_options_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_498_ = lean_st_ref_get(v___y_496_);
v_env_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc_ref(v_env_499_);
lean_dec(v___x_498_);
v___x_500_ = 0;
v_env_501_ = l_Lean_Environment_setRecordingDeps(v_env_499_, v___x_500_);
v___x_502_ = lean_st_ref_get(v___y_494_);
v_toCold_503_ = lean_ctor_get(v___y_495_, 0);
v_mctx_504_ = lean_ctor_get(v___x_502_, 0);
lean_inc_ref(v_mctx_504_);
lean_dec(v___x_502_);
v_lctx_505_ = lean_ctor_get(v___y_493_, 2);
v_options_506_ = lean_ctor_get(v_toCold_503_, 2);
lean_inc_ref(v_options_506_);
lean_inc_ref(v_lctx_505_);
v___x_507_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_507_, 0, v_env_501_);
lean_ctor_set(v___x_507_, 1, v_mctx_504_);
lean_ctor_set(v___x_507_, 2, v_lctx_505_);
lean_ctor_set(v___x_507_, 3, v_options_506_);
v___x_508_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v_msgData_492_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(lean_object* v_msg_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_ref_523_; lean_object* v___x_524_; lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_533_; 
v_ref_523_ = lean_ctor_get(v___y_520_, 2);
v___x_524_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msg_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_533_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
lean_inc(v_ref_523_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_ref_523_);
lean_ctor_set(v___x_529_, 1, v_a_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 1);
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_msg_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object* v_ref_541_, lean_object* v_msg_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_toCold_548_; lean_object* v_currRecDepth_549_; lean_object* v_ref_550_; uint16_t v_optionFlags_551_; uint8_t v_suppressElabErrors_552_; uint8_t v_isRecordingDeps_553_; lean_object* v_ref_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_toCold_548_ = lean_ctor_get(v___y_545_, 0);
v_currRecDepth_549_ = lean_ctor_get(v___y_545_, 1);
v_ref_550_ = lean_ctor_get(v___y_545_, 2);
v_optionFlags_551_ = lean_ctor_get_uint16(v___y_545_, sizeof(void*)*3);
v_suppressElabErrors_552_ = lean_ctor_get_uint8(v___y_545_, sizeof(void*)*3 + 2);
v_isRecordingDeps_553_ = lean_ctor_get_uint8(v___y_545_, sizeof(void*)*3 + 3);
v_ref_554_ = l_Lean_replaceRef(v_ref_541_, v_ref_550_);
lean_inc(v_currRecDepth_549_);
lean_inc_ref(v_toCold_548_);
v___x_555_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_555_, 0, v_toCold_548_);
lean_ctor_set(v___x_555_, 1, v_currRecDepth_549_);
lean_ctor_set(v___x_555_, 2, v_ref_554_);
lean_ctor_set_uint16(v___x_555_, sizeof(void*)*3, v_optionFlags_551_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*3 + 2, v_suppressElabErrors_552_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*3 + 3, v_isRecordingDeps_553_);
v___x_556_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_542_, v___y_543_, v___y_544_, v___x_555_, v___y_546_);
lean_dec_ref_known(v___x_555_, 3);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1(lean_object* v_stx_671_, lean_object* v_terminationBy_x3f_x3f_672_, lean_object* v_terminationBy_x3f_673_, lean_object* v_partialFixpoint_x3f_674_, lean_object* v___x_675_, uint8_t v___x_676_, lean_object* v_toPure_677_, lean_object* v_decreasingBy_x3f_678_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_679_, 0, v_stx_671_);
lean_ctor_set(v___x_679_, 1, v_terminationBy_x3f_x3f_672_);
lean_ctor_set(v___x_679_, 2, v_terminationBy_x3f_673_);
lean_ctor_set(v___x_679_, 3, v_partialFixpoint_x3f_674_);
lean_ctor_set(v___x_679_, 4, v_decreasingBy_x3f_678_);
lean_ctor_set(v___x_679_, 5, v___x_675_);
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*6, v___x_676_);
v___x_680_ = lean_apply_2(v_toPure_677_, lean_box(0), v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed(lean_object* v_stx_681_, lean_object* v_terminationBy_x3f_x3f_682_, lean_object* v_terminationBy_x3f_683_, lean_object* v_partialFixpoint_x3f_684_, lean_object* v___x_685_, lean_object* v___x_686_, lean_object* v_toPure_687_, lean_object* v_decreasingBy_x3f_688_){
_start:
{
uint8_t v___x_2913__boxed_689_; lean_object* v_res_690_; 
v___x_2913__boxed_689_ = lean_unbox(v___x_686_);
v_res_690_ = l_Lean_Elab_elabTerminationHints___redArg___lam__1(v_stx_681_, v_terminationBy_x3f_x3f_682_, v_terminationBy_x3f_683_, v_partialFixpoint_x3f_684_, v___x_685_, v___x_2913__boxed_689_, v_toPure_687_, v_decreasingBy_x3f_688_);
return v_res_690_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* v_stx_695_, lean_object* v_terminationBy_x3f_x3f_696_, lean_object* v_terminationBy_x3f_697_, lean_object* v___x_698_, uint8_t v___x_699_, lean_object* v_toPure_700_, lean_object* v_d_x3f_701_, lean_object* v_toBind_702_, lean_object* v_toFunctor_703_, lean_object* v___f_704_, lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v___x_710_, lean_object* v_partialFixpoint_x3f_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___f_713_; 
v___x_712_ = lean_box(v___x_699_);
lean_inc(v_toPure_700_);
v___f_713_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_713_, 0, v_stx_695_);
lean_closure_set(v___f_713_, 1, v_terminationBy_x3f_x3f_696_);
lean_closure_set(v___f_713_, 2, v_terminationBy_x3f_697_);
lean_closure_set(v___f_713_, 3, v_partialFixpoint_x3f_711_);
lean_closure_set(v___f_713_, 4, v___x_698_);
lean_closure_set(v___f_713_, 5, v___x_712_);
lean_closure_set(v___f_713_, 6, v_toPure_700_);
if (lean_obj_tag(v_d_x3f_701_) == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v___x_707_);
lean_dec_ref(v___x_706_);
lean_dec_ref(v___x_705_);
lean_dec_ref(v___f_704_);
lean_dec_ref(v_toFunctor_703_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_714_);
v___x_716_ = lean_apply_4(v_toBind_702_, lean_box(0), lean_box(0), v___x_715_, v___f_713_);
return v___x_716_;
}
else
{
lean_object* v_val_717_; lean_object* v_map_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_736_; 
v_val_717_ = lean_ctor_get(v_d_x3f_701_, 0);
lean_inc(v_val_717_);
lean_dec_ref_known(v_d_x3f_701_, 1);
v_map_718_ = lean_ctor_get(v_toFunctor_703_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_toFunctor_703_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v_toFunctor_703_, 1);
lean_dec(v_unused_737_);
v___x_720_ = v_toFunctor_703_;
v_isShared_721_ = v_isSharedCheck_736_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_map_718_);
lean_dec(v_toFunctor_703_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_736_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___y_723_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0));
v___x_727_ = l_Lean_Name_mkStr4(v___x_705_, v___x_706_, v___x_707_, v___x_726_);
lean_inc(v_val_717_);
v___x_728_ = l_Lean_Syntax_isOfKind(v_val_717_, v___x_727_);
lean_dec(v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_del_object(v___x_720_);
lean_dec(v_toPure_700_);
v___x_729_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2, &l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2);
v___x_730_ = l_Lean_throwErrorAt___redArg(v_inst_708_, v_inst_709_, v_val_717_, v___x_729_);
v___y_723_ = v___x_730_;
goto v___jp_722_;
}
else
{
lean_object* v_tactic_731_; lean_object* v___x_733_; 
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_708_);
v_tactic_731_ = l_Lean_Syntax_getArg(v_val_717_, v___x_710_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v_tactic_731_);
lean_ctor_set(v___x_720_, 0, v_val_717_);
v___x_733_ = v___x_720_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_val_717_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_tactic_731_);
v___x_733_ = v_reuseFailAlloc_735_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_733_);
v___y_723_ = v___x_734_;
goto v___jp_722_;
}
}
v___jp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_apply_4(v_map_718_, lean_box(0), lean_box(0), v___f_704_, v___y_723_);
v___x_725_ = lean_apply_4(v_toBind_702_, lean_box(0), lean_box(0), v___x_724_, v___f_713_);
return v___x_725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_stx_738_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_739_ = _args[1];
lean_object* v_terminationBy_x3f_740_ = _args[2];
lean_object* v___x_741_ = _args[3];
lean_object* v___x_742_ = _args[4];
lean_object* v_toPure_743_ = _args[5];
lean_object* v_d_x3f_744_ = _args[6];
lean_object* v_toBind_745_ = _args[7];
lean_object* v_toFunctor_746_ = _args[8];
lean_object* v___f_747_ = _args[9];
lean_object* v___x_748_ = _args[10];
lean_object* v___x_749_ = _args[11];
lean_object* v___x_750_ = _args[12];
lean_object* v_inst_751_ = _args[13];
lean_object* v_inst_752_ = _args[14];
lean_object* v___x_753_ = _args[15];
lean_object* v_partialFixpoint_x3f_754_ = _args[16];
_start:
{
uint8_t v___x_2931__boxed_755_; lean_object* v_res_756_; 
v___x_2931__boxed_755_ = lean_unbox(v___x_742_);
v_res_756_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(v_stx_738_, v_terminationBy_x3f_x3f_739_, v_terminationBy_x3f_740_, v___x_741_, v___x_2931__boxed_755_, v_toPure_743_, v_d_x3f_744_, v_toBind_745_, v_toFunctor_746_, v___f_747_, v___x_748_, v___x_749_, v___x_750_, v_inst_751_, v_inst_752_, v___x_753_, v_partialFixpoint_x3f_754_);
lean_dec(v___x_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object* v___f_757_, lean_object* v_partialFixpoint_x3f_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = lean_apply_1(v___f_757_, v_partialFixpoint_x3f_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11(lean_object* v_stx_763_, lean_object* v_terminationBy_x3f_x3f_764_, lean_object* v___x_765_, uint8_t v___x_766_, lean_object* v_toPure_767_, lean_object* v_d_x3f_768_, lean_object* v_toBind_769_, lean_object* v_toFunctor_770_, lean_object* v___f_771_, lean_object* v___x_772_, lean_object* v___x_773_, lean_object* v___x_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v___x_777_, lean_object* v_t_x3f_778_, lean_object* v_terminationBy_x3f_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___f_781_; 
v___x_780_ = lean_box(v___x_766_);
lean_inc(v___x_777_);
lean_inc_ref(v___x_774_);
lean_inc_ref(v___x_773_);
lean_inc_ref(v___x_772_);
lean_inc(v_toBind_769_);
lean_inc(v_toPure_767_);
v___f_781_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed), 17, 16);
lean_closure_set(v___f_781_, 0, v_stx_763_);
lean_closure_set(v___f_781_, 1, v_terminationBy_x3f_x3f_764_);
lean_closure_set(v___f_781_, 2, v_terminationBy_x3f_779_);
lean_closure_set(v___f_781_, 3, v___x_765_);
lean_closure_set(v___f_781_, 4, v___x_780_);
lean_closure_set(v___f_781_, 5, v_toPure_767_);
lean_closure_set(v___f_781_, 6, v_d_x3f_768_);
lean_closure_set(v___f_781_, 7, v_toBind_769_);
lean_closure_set(v___f_781_, 8, v_toFunctor_770_);
lean_closure_set(v___f_781_, 9, v___f_771_);
lean_closure_set(v___f_781_, 10, v___x_772_);
lean_closure_set(v___f_781_, 11, v___x_773_);
lean_closure_set(v___f_781_, 12, v___x_774_);
lean_closure_set(v___f_781_, 13, v_inst_775_);
lean_closure_set(v___f_781_, 14, v_inst_776_);
lean_closure_set(v___f_781_, 15, v___x_777_);
if (lean_obj_tag(v_t_x3f_778_) == 1)
{
lean_object* v_val_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_859_; 
v_val_782_ = lean_ctor_get(v_t_x3f_778_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v_t_x3f_778_);
if (v_isSharedCheck_859_ == 0)
{
v___x_784_ = v_t_x3f_778_;
v_isShared_785_ = v_isSharedCheck_859_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_val_782_);
lean_dec(v_t_x3f_778_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_859_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_786_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_774_);
lean_inc_ref(v___x_773_);
lean_inc_ref(v___x_772_);
v___x_787_ = l_Lean_Name_mkStr4(v___x_772_, v___x_773_, v___x_774_, v___x_786_);
lean_inc(v_val_782_);
v___x_788_ = l_Lean_Syntax_isOfKind(v_val_782_, v___x_787_);
lean_dec(v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_789_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_774_);
lean_inc_ref(v___x_773_);
lean_inc_ref(v___x_772_);
v___x_790_ = l_Lean_Name_mkStr4(v___x_772_, v___x_773_, v___x_774_, v___x_789_);
lean_inc(v_val_782_);
v___x_791_ = l_Lean_Syntax_isOfKind(v_val_782_, v___x_790_);
lean_dec(v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_792_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_793_ = l_Lean_Name_mkStr4(v___x_772_, v___x_773_, v___x_774_, v___x_792_);
lean_inc(v_val_782_);
v___x_794_ = l_Lean_Syntax_isOfKind(v_val_782_, v___x_793_);
lean_dec(v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___f_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_del_object(v___x_784_);
lean_dec(v_val_782_);
lean_dec(v___x_777_);
v___f_795_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_795_, 0, v___f_781_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_796_);
v___x_798_ = lean_apply_4(v_toBind_769_, lean_box(0), lean_box(0), v___x_797_, v___f_795_);
return v___x_798_;
}
else
{
lean_object* v___f_799_; lean_object* v_term_x3f_801_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___f_799_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_799_, 0, v___f_781_);
v___x_809_ = l_Lean_Syntax_getArg(v_val_782_, v___x_777_);
v___x_810_ = l_Lean_Syntax_isNone(v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_809_);
v___x_812_ = l_Lean_Syntax_matchesNull(v___x_809_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v___x_809_);
lean_del_object(v___x_784_);
lean_dec(v_val_782_);
lean_dec(v___x_777_);
v___x_813_ = lean_box(0);
v___x_814_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_813_);
v___x_815_ = lean_apply_4(v_toBind_769_, lean_box(0), lean_box(0), v___x_814_, v___f_799_);
return v___x_815_;
}
else
{
lean_object* v_term_x3f_816_; lean_object* v___x_817_; 
v_term_x3f_816_ = l_Lean_Syntax_getArg(v___x_809_, v___x_777_);
lean_dec(v___x_777_);
lean_dec(v___x_809_);
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v_term_x3f_816_);
v_term_x3f_801_ = v___x_817_;
goto v___jp_800_;
}
}
else
{
lean_object* v___x_818_; 
lean_dec(v___x_809_);
lean_dec(v___x_777_);
v___x_818_ = lean_box(0);
v_term_x3f_801_ = v___x_818_;
goto v___jp_800_;
}
v___jp_800_:
{
uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_802_ = 2;
v___x_803_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_803_, 0, v_val_782_);
lean_ctor_set(v___x_803_, 1, v_term_x3f_801_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*2, v___x_802_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_803_);
v___x_805_ = v___x_784_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_808_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_805_);
v___x_807_ = lean_apply_4(v_toBind_769_, lean_box(0), lean_box(0), v___x_806_, v___f_799_);
return v___x_807_;
}
}
}
}
else
{
lean_object* v___f_819_; lean_object* v_term_x3f_821_; lean_object* v___x_829_; uint8_t v___x_830_; 
lean_dec_ref(v___x_774_);
lean_dec_ref(v___x_773_);
lean_dec_ref(v___x_772_);
v___f_819_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_819_, 0, v___f_781_);
v___x_829_ = l_Lean_Syntax_getArg(v_val_782_, v___x_777_);
v___x_830_ = l_Lean_Syntax_isNone(v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_829_);
v___x_832_ = l_Lean_Syntax_matchesNull(v___x_829_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec(v___x_829_);
lean_del_object(v___x_784_);
lean_dec(v_val_782_);
lean_dec(v___x_777_);
v___x_833_ = lean_box(0);
v___x_834_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_833_);
v___x_835_ = lean_apply_4(v_toBind_769_, lean_box(0), lean_box(0), v___x_834_, v___f_819_);
return v___x_835_;
}
else
{
lean_object* v_term_x3f_836_; lean_object* v___x_837_; 
v_term_x3f_836_ = l_Lean_Syntax_getArg(v___x_829_, v___x_777_);
lean_dec(v___x_777_);
lean_dec(v___x_829_);
v___x_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_837_, 0, v_term_x3f_836_);
v_term_x3f_821_ = v___x_837_;
goto v___jp_820_;
}
}
else
{
lean_object* v___x_838_; 
lean_dec(v___x_829_);
lean_dec(v___x_777_);
v___x_838_ = lean_box(0);
v_term_x3f_821_ = v___x_838_;
goto v___jp_820_;
}
v___jp_820_:
{
uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_822_ = 1;
v___x_823_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_823_, 0, v_val_782_);
lean_ctor_set(v___x_823_, 1, v_term_x3f_821_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*2, v___x_822_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_823_);
v___x_825_ = v___x_784_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_828_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_825_);
v___x_827_ = lean_apply_4(v_toBind_769_, lean_box(0), lean_box(0), v___x_826_, v___f_819_);
return v___x_827_;
}
}
}
}
else
{
lean_object* v___f_839_; lean_object* v_term_x3f_841_; lean_object* v___x_849_; uint8_t v___x_850_; 
lean_dec_ref(v___x_774_);
lean_dec_ref(v___x_773_);
lean_dec_ref(v___x_772_);
v___f_839_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_839_, 0, v___f_781_);
v___x_849_ = l_Lean_Syntax_getArg(v_val_782_, v___x_777_);
v___x_850_ = l_Lean_Syntax_isNone(v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_849_);
v___x_852_ = l_Lean_Syntax_matchesNull(v___x_849_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v___x_849_);
lean_del_object(v___x_784_);
lean_dec(v_val_782_);
lean_dec(v___x_777_);
v___x_853_ = lean_box(0);
v___x_854_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_853_);
v___x_855_ = lean_apply_4(v_toBind_769_, lean_box(0), lean_box(0), v___x_854_, v___f_839_);
return v___x_855_;
}
else
{
lean_object* v_term_x3f_856_; lean_object* v___x_857_; 
v_term_x3f_856_ = l_Lean_Syntax_getArg(v___x_849_, v___x_777_);
lean_dec(v___x_777_);
lean_dec(v___x_849_);
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v_term_x3f_856_);
v_term_x3f_841_ = v___x_857_;
goto v___jp_840_;
}
}
else
{
lean_object* v___x_858_; 
lean_dec(v___x_849_);
lean_dec(v___x_777_);
v___x_858_ = lean_box(0);
v_term_x3f_841_ = v___x_858_;
goto v___jp_840_;
}
v___jp_840_:
{
uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_842_ = 0;
v___x_843_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_843_, 0, v_val_782_);
lean_ctor_set(v___x_843_, 1, v_term_x3f_841_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*2, v___x_842_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_843_);
v___x_845_ = v___x_784_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_848_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_845_);
v___x_847_ = lean_apply_4(v_toBind_769_, lean_box(0), lean_box(0), v___x_846_, v___f_839_);
return v___x_847_;
}
}
}
}
}
else
{
lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v_t_x3f_778_);
lean_dec(v___x_777_);
lean_dec_ref(v___x_774_);
lean_dec_ref(v___x_773_);
lean_dec_ref(v___x_772_);
v___f_860_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3), 2, 1);
lean_closure_set(v___f_860_, 0, v___f_781_);
v___x_861_ = lean_box(0);
v___x_862_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_861_);
v___x_863_ = lean_apply_4(v_toBind_769_, lean_box(0), lean_box(0), v___x_862_, v___f_860_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_stx_864_ = _args[0];
lean_object* v_terminationBy_x3f_x3f_865_ = _args[1];
lean_object* v___x_866_ = _args[2];
lean_object* v___x_867_ = _args[3];
lean_object* v_toPure_868_ = _args[4];
lean_object* v_d_x3f_869_ = _args[5];
lean_object* v_toBind_870_ = _args[6];
lean_object* v_toFunctor_871_ = _args[7];
lean_object* v___f_872_ = _args[8];
lean_object* v___x_873_ = _args[9];
lean_object* v___x_874_ = _args[10];
lean_object* v___x_875_ = _args[11];
lean_object* v_inst_876_ = _args[12];
lean_object* v_inst_877_ = _args[13];
lean_object* v___x_878_ = _args[14];
lean_object* v_t_x3f_879_ = _args[15];
lean_object* v_terminationBy_x3f_880_ = _args[16];
_start:
{
uint8_t v___x_3020__boxed_881_; lean_object* v_res_882_; 
v___x_3020__boxed_881_ = lean_unbox(v___x_867_);
v_res_882_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11(v_stx_864_, v_terminationBy_x3f_x3f_865_, v___x_866_, v___x_3020__boxed_881_, v_toPure_868_, v_d_x3f_869_, v_toBind_870_, v_toFunctor_871_, v___f_872_, v___x_873_, v___x_874_, v___x_875_, v_inst_876_, v_inst_877_, v___x_878_, v_t_x3f_879_, v_terminationBy_x3f_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* v___f_883_, lean_object* v_terminationBy_x3f_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = lean_apply_1(v___f_883_, v_terminationBy_x3f_884_);
return v___x_885_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4));
v___x_893_ = l_Lean_stringToMessageData(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* v_stx_894_, lean_object* v___x_895_, uint8_t v___x_896_, lean_object* v_toPure_897_, lean_object* v_d_x3f_898_, lean_object* v_toBind_899_, lean_object* v_toFunctor_900_, lean_object* v___f_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v___x_907_, lean_object* v_t_x3f_908_, lean_object* v_terminationBy_x3f_x3f_909_){
_start:
{
lean_object* v___x_910_; lean_object* v___f_911_; 
v___x_910_ = lean_box(v___x_896_);
lean_inc(v_t_x3f_908_);
lean_inc(v___x_907_);
lean_inc_ref(v_inst_906_);
lean_inc_ref(v_inst_905_);
lean_inc_ref(v___x_904_);
lean_inc_ref(v___x_903_);
lean_inc_ref(v___x_902_);
lean_inc(v_toBind_899_);
lean_inc(v_toPure_897_);
lean_inc(v___x_895_);
v___f_911_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_911_, 0, v_stx_894_);
lean_closure_set(v___f_911_, 1, v_terminationBy_x3f_x3f_909_);
lean_closure_set(v___f_911_, 2, v___x_895_);
lean_closure_set(v___f_911_, 3, v___x_910_);
lean_closure_set(v___f_911_, 4, v_toPure_897_);
lean_closure_set(v___f_911_, 5, v_d_x3f_898_);
lean_closure_set(v___f_911_, 6, v_toBind_899_);
lean_closure_set(v___f_911_, 7, v_toFunctor_900_);
lean_closure_set(v___f_911_, 8, v___f_901_);
lean_closure_set(v___f_911_, 9, v___x_902_);
lean_closure_set(v___f_911_, 10, v___x_903_);
lean_closure_set(v___f_911_, 11, v___x_904_);
lean_closure_set(v___f_911_, 12, v_inst_905_);
lean_closure_set(v___f_911_, 13, v_inst_906_);
lean_closure_set(v___f_911_, 14, v___x_907_);
lean_closure_set(v___f_911_, 15, v_t_x3f_908_);
if (lean_obj_tag(v_t_x3f_908_) == 1)
{
lean_object* v_val_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_1024_; 
v_val_912_ = lean_ctor_get(v_t_x3f_908_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_t_x3f_908_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_914_ = v_t_x3f_908_;
v_isShared_915_ = v_isSharedCheck_1024_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_val_912_);
lean_dec(v_t_x3f_908_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_1024_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_916_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0));
lean_inc_ref(v___x_904_);
lean_inc_ref(v___x_903_);
lean_inc_ref(v___x_902_);
v___x_917_ = l_Lean_Name_mkStr4(v___x_902_, v___x_903_, v___x_904_, v___x_916_);
lean_inc(v_val_912_);
v___x_918_ = l_Lean_Syntax_isOfKind(v_val_912_, v___x_917_);
lean_dec(v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
lean_del_object(v___x_914_);
lean_dec(v___x_895_);
v___x_919_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1));
lean_inc_ref(v___x_904_);
lean_inc_ref(v___x_903_);
lean_inc_ref(v___x_902_);
v___x_920_ = l_Lean_Name_mkStr4(v___x_902_, v___x_903_, v___x_904_, v___x_919_);
lean_inc(v_val_912_);
v___x_921_ = l_Lean_Syntax_isOfKind(v_val_912_, v___x_920_);
lean_dec(v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_922_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0));
lean_inc_ref(v___x_904_);
lean_inc_ref(v___x_903_);
lean_inc_ref(v___x_902_);
v___x_923_ = l_Lean_Name_mkStr4(v___x_902_, v___x_903_, v___x_904_, v___x_922_);
lean_inc(v_val_912_);
v___x_924_ = l_Lean_Syntax_isOfKind(v_val_912_, v___x_923_);
lean_dec(v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_925_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1));
lean_inc_ref(v___x_904_);
lean_inc_ref(v___x_903_);
lean_inc_ref(v___x_902_);
v___x_926_ = l_Lean_Name_mkStr4(v___x_902_, v___x_903_, v___x_904_, v___x_925_);
lean_inc(v_val_912_);
v___x_927_ = l_Lean_Syntax_isOfKind(v_val_912_, v___x_926_);
lean_dec(v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_928_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2));
v___x_929_ = l_Lean_Name_mkStr4(v___x_902_, v___x_903_, v___x_904_, v___x_928_);
lean_inc(v_val_912_);
v___x_930_ = l_Lean_Syntax_isOfKind(v_val_912_, v___x_929_);
lean_dec(v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v___x_907_);
lean_dec(v_toPure_897_);
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_931_, 0, v___f_911_);
v___x_932_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_933_ = l_Lean_throwErrorAt___redArg(v_inst_905_, v_inst_906_, v_val_912_, v___x_932_);
v___x_934_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_933_, v___f_931_);
return v___x_934_;
}
else
{
lean_object* v___f_935_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___f_935_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_935_, 0, v___f_911_);
v___x_940_ = l_Lean_Syntax_getArg(v_val_912_, v___x_907_);
lean_dec(v___x_907_);
v___x_941_ = l_Lean_Syntax_isNone(v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = lean_unsigned_to_nat(2u);
v___x_943_ = l_Lean_Syntax_matchesNull(v___x_940_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec(v_toPure_897_);
v___x_944_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_945_ = l_Lean_throwErrorAt___redArg(v_inst_905_, v_inst_906_, v_val_912_, v___x_944_);
v___x_946_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_945_, v___f_935_);
return v___x_946_;
}
else
{
lean_dec(v_val_912_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_inst_905_);
goto v___jp_936_;
}
}
else
{
lean_dec(v___x_940_);
lean_dec(v_val_912_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_inst_905_);
goto v___jp_936_;
}
v___jp_936_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_box(0);
v___x_938_ = lean_apply_2(v_toPure_897_, lean_box(0), v___x_937_);
v___x_939_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_938_, v___f_935_);
return v___x_939_;
}
}
}
else
{
lean_object* v___f_947_; lean_object* v___x_952_; uint8_t v___x_953_; 
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v___x_902_);
v___f_947_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_947_, 0, v___f_911_);
v___x_952_ = l_Lean_Syntax_getArg(v_val_912_, v___x_907_);
lean_dec(v___x_907_);
v___x_953_ = l_Lean_Syntax_isNone(v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = lean_unsigned_to_nat(2u);
v___x_955_ = l_Lean_Syntax_matchesNull(v___x_952_, v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_toPure_897_);
v___x_956_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_957_ = l_Lean_throwErrorAt___redArg(v_inst_905_, v_inst_906_, v_val_912_, v___x_956_);
v___x_958_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_957_, v___f_947_);
return v___x_958_;
}
else
{
lean_dec(v_val_912_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_inst_905_);
goto v___jp_948_;
}
}
else
{
lean_dec(v___x_952_);
lean_dec(v_val_912_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_inst_905_);
goto v___jp_948_;
}
v___jp_948_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_box(0);
v___x_950_ = lean_apply_2(v_toPure_897_, lean_box(0), v___x_949_);
v___x_951_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_950_, v___f_947_);
return v___x_951_;
}
}
}
else
{
lean_object* v___f_959_; lean_object* v___x_964_; uint8_t v___x_965_; 
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v___x_902_);
v___f_959_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_959_, 0, v___f_911_);
v___x_964_ = l_Lean_Syntax_getArg(v_val_912_, v___x_907_);
lean_dec(v___x_907_);
v___x_965_ = l_Lean_Syntax_isNone(v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_unsigned_to_nat(2u);
v___x_967_ = l_Lean_Syntax_matchesNull(v___x_964_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec(v_toPure_897_);
v___x_968_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_969_ = l_Lean_throwErrorAt___redArg(v_inst_905_, v_inst_906_, v_val_912_, v___x_968_);
v___x_970_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_969_, v___f_959_);
return v___x_970_;
}
else
{
lean_dec(v_val_912_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_inst_905_);
goto v___jp_960_;
}
}
else
{
lean_dec(v___x_964_);
lean_dec(v_val_912_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_inst_905_);
goto v___jp_960_;
}
v___jp_960_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = lean_box(0);
v___x_962_ = lean_apply_2(v_toPure_897_, lean_box(0), v___x_961_);
v___x_963_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_962_, v___f_959_);
return v___x_963_;
}
}
}
else
{
lean_object* v___f_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec(v_val_912_);
lean_dec(v___x_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_inst_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v___x_902_);
v___f_971_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_971_, 0, v___f_911_);
v___x_972_ = lean_box(0);
v___x_973_ = lean_apply_2(v_toPure_897_, lean_box(0), v___x_972_);
v___x_974_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_973_, v___f_971_);
return v___x_974_;
}
}
else
{
lean_object* v___f_975_; lean_object* v___y_977_; lean_object* v___y_978_; uint8_t v___y_979_; uint8_t v___y_980_; uint8_t v___y_988_; lean_object* v___y_989_; uint8_t v___y_990_; lean_object* v_s_997_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v___x_902_);
v___f_975_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_975_, 0, v___f_911_);
v___x_1015_ = l_Lean_Syntax_getArg(v_val_912_, v___x_907_);
v___x_1016_ = l_Lean_Syntax_isNone(v___x_1015_);
if (v___x_1016_ == 0)
{
uint8_t v___x_1017_; 
lean_inc(v___x_1015_);
v___x_1017_ = l_Lean_Syntax_matchesNull(v___x_1015_, v___x_907_);
lean_dec(v___x_907_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec(v___x_1015_);
lean_del_object(v___x_914_);
lean_dec(v_toPure_897_);
lean_dec(v___x_895_);
v___x_1018_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1019_ = l_Lean_throwErrorAt___redArg(v_inst_905_, v_inst_906_, v_val_912_, v___x_1018_);
v___x_1020_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_1019_, v___f_975_);
return v___x_1020_;
}
else
{
lean_object* v_s_1021_; lean_object* v___x_1022_; 
v_s_1021_ = l_Lean_Syntax_getArg(v___x_1015_, v___x_895_);
lean_dec(v___x_1015_);
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v_s_1021_);
v_s_997_ = v___x_1022_;
goto v___jp_996_;
}
}
else
{
lean_object* v___x_1023_; 
lean_dec(v___x_1015_);
lean_dec(v___x_907_);
v___x_1023_ = lean_box(0);
v_s_997_ = v___x_1023_;
goto v___jp_996_;
}
v___jp_976_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_981_, 0, v_val_912_);
lean_ctor_set(v___x_981_, 1, v___y_978_);
lean_ctor_set(v___x_981_, 2, v___y_977_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*3, v___y_980_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*3 + 1, v___y_979_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_981_);
v___x_983_ = v___x_914_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_986_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_apply_2(v_toPure_897_, lean_box(0), v___x_983_);
v___x_985_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_984_, v___f_975_);
return v___x_985_;
}
}
v___jp_987_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_991_ = lean_mk_empty_array_with_capacity(v___x_895_);
lean_dec(v___x_895_);
v___x_992_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_992_, 0, v_val_912_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
lean_ctor_set(v___x_992_, 2, v___y_989_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*3, v___y_990_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*3 + 1, v___y_988_);
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
v___x_994_ = lean_apply_2(v_toPure_897_, lean_box(0), v___x_993_);
v___x_995_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_994_, v___f_975_);
return v___x_995_;
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_998_ = lean_unsigned_to_nat(2u);
v___x_999_ = l_Lean_Syntax_getArg(v_val_912_, v___x_998_);
lean_inc(v___x_999_);
v___x_1000_ = l_Lean_Syntax_matchesNull(v___x_999_, v___x_998_);
if (v___x_1000_ == 0)
{
uint8_t v___x_1001_; 
lean_del_object(v___x_914_);
v___x_1001_ = l_Lean_Syntax_matchesNull(v___x_999_, v___x_895_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec(v_s_997_);
lean_dec(v_toPure_897_);
lean_dec(v___x_895_);
v___x_1002_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
v___x_1003_ = l_Lean_throwErrorAt___redArg(v_inst_905_, v_inst_906_, v_val_912_, v___x_1002_);
v___x_1004_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_1003_, v___f_975_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; lean_object* v_body_1006_; 
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_inst_905_);
v___x_1005_ = lean_unsigned_to_nat(3u);
v_body_1006_ = l_Lean_Syntax_getArg(v_val_912_, v___x_1005_);
if (lean_obj_tag(v_s_997_) == 0)
{
v___y_988_ = v___x_1000_;
v___y_989_ = v_body_1006_;
v___y_990_ = v___x_1000_;
goto v___jp_987_;
}
else
{
lean_dec_ref_known(v_s_997_, 1);
v___y_988_ = v___x_1000_;
v___y_989_ = v_body_1006_;
v___y_990_ = v___x_1001_;
goto v___jp_987_;
}
}
}
else
{
lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = l_Lean_Syntax_getArg(v___x_999_, v___x_895_);
lean_dec(v___x_999_);
lean_inc(v___x_1007_);
v___x_1008_ = l_Lean_Syntax_matchesNull(v___x_1007_, v___x_895_);
lean_dec(v___x_895_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v_body_1010_; lean_object* v_vars_1011_; 
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_inst_905_);
v___x_1009_ = lean_unsigned_to_nat(3u);
v_body_1010_ = l_Lean_Syntax_getArg(v_val_912_, v___x_1009_);
v_vars_1011_ = l_Lean_Syntax_getArgs(v___x_1007_);
lean_dec(v___x_1007_);
if (lean_obj_tag(v_s_997_) == 0)
{
v___y_977_ = v_body_1010_;
v___y_978_ = v_vars_1011_;
v___y_979_ = v___x_1008_;
v___y_980_ = v___x_1008_;
goto v___jp_976_;
}
else
{
lean_dec_ref_known(v_s_997_, 1);
v___y_977_ = v_body_1010_;
v___y_978_ = v_vars_1011_;
v___y_979_ = v___x_1008_;
v___y_980_ = v___x_1000_;
goto v___jp_976_;
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec(v___x_1007_);
lean_dec(v_s_997_);
lean_del_object(v___x_914_);
lean_dec(v_toPure_897_);
v___x_1012_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5, &l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once, _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
v___x_1013_ = l_Lean_throwErrorAt___redArg(v_inst_905_, v_inst_906_, v_val_912_, v___x_1012_);
v___x_1014_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_1013_, v___f_975_);
return v___x_1014_;
}
}
}
}
}
}
else
{
lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v_t_x3f_908_);
lean_dec(v___x_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_inst_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v___x_902_);
lean_dec(v___x_895_);
v___f_1025_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1025_, 0, v___f_911_);
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_apply_2(v_toPure_897_, lean_box(0), v___x_1026_);
v___x_1028_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_1027_, v___f_1025_);
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed(lean_object* v_stx_1029_, lean_object* v___x_1030_, lean_object* v___x_1031_, lean_object* v_toPure_1032_, lean_object* v_d_x3f_1033_, lean_object* v_toBind_1034_, lean_object* v_toFunctor_1035_, lean_object* v___f_1036_, lean_object* v___x_1037_, lean_object* v___x_1038_, lean_object* v___x_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v___x_1042_, lean_object* v_t_x3f_1043_, lean_object* v_terminationBy_x3f_x3f_1044_){
_start:
{
uint8_t v___x_3244__boxed_1045_; lean_object* v_res_1046_; 
v___x_3244__boxed_1045_ = lean_unbox(v___x_1031_);
v_res_1046_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19(v_stx_1029_, v___x_1030_, v___x_3244__boxed_1045_, v_toPure_1032_, v_d_x3f_1033_, v_toBind_1034_, v_toFunctor_1035_, v___f_1036_, v___x_1037_, v___x_1038_, v___x_1039_, v_inst_1040_, v_inst_1041_, v___x_1042_, v_t_x3f_1043_, v_terminationBy_x3f_x3f_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* v___f_1047_, lean_object* v_terminationBy_x3f_x3f_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_apply_1(v___f_1047_, v_terminationBy_x3f_x3f_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_stx_1074_){
_start:
{
if (lean_obj_tag(v_stx_1074_) == 0)
{
lean_object* v_toApplicative_1075_; lean_object* v_toPure_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_toApplicative_1075_ = lean_ctor_get(v_inst_1072_, 0);
lean_inc_ref(v_toApplicative_1075_);
lean_dec_ref(v_inst_1073_);
lean_dec_ref(v_inst_1072_);
v_toPure_1076_ = lean_ctor_get(v_toApplicative_1075_, 1);
lean_inc(v_toPure_1076_);
lean_dec_ref(v_toApplicative_1075_);
v___x_1077_ = 1;
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1080_, 0, v_stx_1074_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
lean_ctor_set(v___x_1080_, 2, v___x_1079_);
lean_ctor_set(v___x_1080_, 3, v___x_1079_);
lean_ctor_set(v___x_1080_, 4, v___x_1079_);
lean_ctor_set(v___x_1080_, 5, v___x_1078_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*6, v___x_1077_);
v___x_1081_ = lean_apply_2(v_toPure_1076_, lean_box(0), v___x_1080_);
return v___x_1081_;
}
else
{
lean_object* v_toApplicative_1082_; lean_object* v_toBind_1083_; lean_object* v_toFunctor_1084_; lean_object* v_toPure_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v_toApplicative_1082_ = lean_ctor_get(v_inst_1072_, 0);
v_toBind_1083_ = lean_ctor_get(v_inst_1072_, 1);
v_toFunctor_1084_ = lean_ctor_get(v_toApplicative_1082_, 0);
v_toPure_1085_ = lean_ctor_get(v_toApplicative_1082_, 1);
v___x_1086_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__0));
v___x_1087_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__1));
v___x_1088_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__2));
v___x_1089_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__4));
lean_inc(v_stx_1074_);
v___x_1090_ = l_Lean_Syntax_isOfKind(v_stx_1074_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1091_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1092_ = lean_box(0);
lean_inc_n(v_stx_1074_, 2);
v___x_1093_ = l_Lean_Syntax_formatStx(v_stx_1074_, v___x_1092_, v___x_1090_);
v___x_1094_ = l_Std_Format_defWidth;
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = l_Std_Format_pretty(v___x_1093_, v___x_1094_, v___x_1095_, v___x_1095_);
v___x_1097_ = lean_string_append(v___x_1091_, v___x_1096_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1099_ = lean_string_append(v___x_1097_, v___x_1098_);
v___x_1100_ = l_Lean_Syntax_getKind(v_stx_1074_);
v___x_1101_ = 1;
v___x_1102_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1100_, v___x_1101_);
v___x_1103_ = lean_string_append(v___x_1099_, v___x_1102_);
lean_dec_ref(v___x_1102_);
v___x_1104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
v___x_1105_ = l_Lean_MessageData_ofFormat(v___x_1104_);
v___x_1106_ = l_Lean_throwErrorAt___redArg(v_inst_1072_, v_inst_1073_, v_stx_1074_, v___x_1105_);
return v___x_1106_;
}
else
{
lean_object* v___f_1107_; lean_object* v___x_1108_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v_d_x3f_1113_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v_t_x3f_1144_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___f_1107_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__7));
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1181_ = l_Lean_Syntax_getArg(v_stx_1074_, v___x_1108_);
v___x_1182_ = l_Lean_Syntax_isNone(v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1181_);
v___x_1184_ = l_Lean_Syntax_matchesNull(v___x_1181_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec(v___x_1181_);
v___x_1185_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1186_ = lean_box(0);
lean_inc_n(v_stx_1074_, 2);
v___x_1187_ = l_Lean_Syntax_formatStx(v_stx_1074_, v___x_1186_, v___x_1184_);
v___x_1188_ = l_Std_Format_defWidth;
v___x_1189_ = l_Std_Format_pretty(v___x_1187_, v___x_1188_, v___x_1108_, v___x_1108_);
v___x_1190_ = lean_string_append(v___x_1185_, v___x_1189_);
lean_dec_ref(v___x_1189_);
v___x_1191_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1192_ = lean_string_append(v___x_1190_, v___x_1191_);
v___x_1193_ = l_Lean_Syntax_getKind(v_stx_1074_);
v___x_1194_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1193_, v___x_1090_);
v___x_1195_ = lean_string_append(v___x_1192_, v___x_1194_);
lean_dec_ref(v___x_1194_);
v___x_1196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
v___x_1197_ = l_Lean_MessageData_ofFormat(v___x_1196_);
v___x_1198_ = l_Lean_throwErrorAt___redArg(v_inst_1072_, v_inst_1073_, v_stx_1074_, v___x_1197_);
return v___x_1198_;
}
else
{
lean_object* v_t_x3f_1199_; lean_object* v___x_1200_; 
v_t_x3f_1199_ = l_Lean_Syntax_getArg(v___x_1181_, v___x_1108_);
lean_dec(v___x_1181_);
v___x_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1200_, 0, v_t_x3f_1199_);
v_t_x3f_1144_ = v___x_1200_;
goto v___jp_1143_;
}
}
else
{
lean_object* v___x_1201_; 
lean_dec(v___x_1181_);
v___x_1201_ = lean_box(0);
v_t_x3f_1144_ = v___x_1201_;
goto v___jp_1143_;
}
v___jp_1109_:
{
lean_object* v___x_1114_; lean_object* v___f_1115_; 
v___x_1114_ = lean_box(v___x_1090_);
lean_inc(v_toBind_1083_);
lean_inc(v_toPure_1085_);
v___f_1115_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed), 16, 15);
lean_closure_set(v___f_1115_, 0, v_stx_1074_);
lean_closure_set(v___f_1115_, 1, v___x_1108_);
lean_closure_set(v___f_1115_, 2, v___x_1114_);
lean_closure_set(v___f_1115_, 3, v_toPure_1085_);
lean_closure_set(v___f_1115_, 4, v_d_x3f_1113_);
lean_closure_set(v___f_1115_, 5, v_toBind_1083_);
lean_closure_set(v___f_1115_, 6, v_toFunctor_1084_);
lean_closure_set(v___f_1115_, 7, v___f_1107_);
lean_closure_set(v___f_1115_, 8, v___x_1086_);
lean_closure_set(v___f_1115_, 9, v___x_1087_);
lean_closure_set(v___f_1115_, 10, v___x_1088_);
lean_closure_set(v___f_1115_, 11, v_inst_1072_);
lean_closure_set(v___f_1115_, 12, v_inst_1073_);
lean_closure_set(v___f_1115_, 13, v___y_1110_);
lean_closure_set(v___f_1115_, 14, v___y_1111_);
if (lean_obj_tag(v___y_1112_) == 1)
{
lean_object* v_val_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1132_; 
v_val_1116_ = lean_ctor_get(v___y_1112_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___y_1112_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1118_ = v___y_1112_;
v_isShared_1119_ = v_isSharedCheck_1132_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_val_1116_);
lean_dec(v___y_1112_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1132_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__8));
lean_inc(v_val_1116_);
v___x_1121_ = l_Lean_Syntax_isOfKind(v_val_1116_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_del_object(v___x_1118_);
lean_dec(v_val_1116_);
v___f_1122_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1122_, 0, v___f_1115_);
v___x_1123_ = lean_box(0);
v___x_1124_ = lean_apply_2(v_toPure_1085_, lean_box(0), v___x_1123_);
v___x_1125_ = lean_apply_4(v_toBind_1083_, lean_box(0), lean_box(0), v___x_1124_, v___f_1122_);
return v___x_1125_;
}
else
{
lean_object* v___f_1126_; lean_object* v___x_1128_; 
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1126_, 0, v___f_1115_);
if (v_isShared_1119_ == 0)
{
v___x_1128_ = v___x_1118_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_val_1116_);
v___x_1128_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_apply_2(v_toPure_1085_, lean_box(0), v___x_1128_);
v___x_1130_ = lean_apply_4(v_toBind_1083_, lean_box(0), lean_box(0), v___x_1129_, v___f_1126_);
return v___x_1130_;
}
}
}
}
else
{
lean_object* v___f_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v___y_1112_);
v___f_1133_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1133_, 0, v___f_1115_);
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_apply_2(v_toPure_1085_, lean_box(0), v___x_1134_);
v___x_1136_ = lean_apply_4(v_toBind_1083_, lean_box(0), lean_box(0), v___x_1135_, v___f_1133_);
return v___x_1136_;
}
}
v___jp_1137_:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___y_1140_);
v___y_1110_ = v___y_1138_;
v___y_1111_ = v___y_1139_;
v___y_1112_ = v___y_1141_;
v_d_x3f_1113_ = v___x_1142_;
goto v___jp_1109_;
}
v___jp_1143_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = l_Lean_Syntax_getArg(v_stx_1074_, v___x_1145_);
v___x_1147_ = l_Lean_Syntax_isNone(v___x_1146_);
if (v___x_1147_ == 0)
{
uint8_t v___x_1148_; 
lean_inc(v___x_1146_);
v___x_1148_ = l_Lean_Syntax_matchesNull(v___x_1146_, v___x_1145_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec(v___x_1146_);
lean_dec(v_t_x3f_1144_);
v___x_1149_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1150_ = lean_box(0);
lean_inc_n(v_stx_1074_, 2);
v___x_1151_ = l_Lean_Syntax_formatStx(v_stx_1074_, v___x_1150_, v___x_1148_);
v___x_1152_ = l_Std_Format_defWidth;
v___x_1153_ = l_Std_Format_pretty(v___x_1151_, v___x_1152_, v___x_1108_, v___x_1108_);
v___x_1154_ = lean_string_append(v___x_1149_, v___x_1153_);
lean_dec_ref(v___x_1153_);
v___x_1155_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1156_ = lean_string_append(v___x_1154_, v___x_1155_);
v___x_1157_ = l_Lean_Syntax_getKind(v_stx_1074_);
v___x_1158_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1157_, v___x_1090_);
v___x_1159_ = lean_string_append(v___x_1156_, v___x_1158_);
lean_dec_ref(v___x_1158_);
v___x_1160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
v___x_1161_ = l_Lean_MessageData_ofFormat(v___x_1160_);
v___x_1162_ = l_Lean_throwErrorAt___redArg(v_inst_1072_, v_inst_1073_, v_stx_1074_, v___x_1161_);
return v___x_1162_;
}
else
{
lean_object* v_d_x3f_1163_; 
v_d_x3f_1163_ = l_Lean_Syntax_getArg(v___x_1146_, v___x_1108_);
lean_dec(v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__9));
lean_inc(v_d_x3f_1163_);
v___x_1165_ = l_Lean_Syntax_isOfKind(v_d_x3f_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec(v_d_x3f_1163_);
lean_dec(v_t_x3f_1144_);
v___x_1166_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__5));
v___x_1167_ = lean_box(0);
lean_inc_n(v_stx_1074_, 2);
v___x_1168_ = l_Lean_Syntax_formatStx(v_stx_1074_, v___x_1167_, v___x_1147_);
v___x_1169_ = l_Std_Format_defWidth;
v___x_1170_ = l_Std_Format_pretty(v___x_1168_, v___x_1169_, v___x_1108_, v___x_1108_);
v___x_1171_ = lean_string_append(v___x_1166_, v___x_1170_);
lean_dec_ref(v___x_1170_);
v___x_1172_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___redArg___closed__6));
v___x_1173_ = lean_string_append(v___x_1171_, v___x_1172_);
v___x_1174_ = l_Lean_Syntax_getKind(v_stx_1074_);
v___x_1175_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1174_, v___x_1148_);
v___x_1176_ = lean_string_append(v___x_1173_, v___x_1175_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
v___x_1178_ = l_Lean_MessageData_ofFormat(v___x_1177_);
v___x_1179_ = l_Lean_throwErrorAt___redArg(v_inst_1072_, v_inst_1073_, v_stx_1074_, v___x_1178_);
return v___x_1179_;
}
else
{
lean_inc(v_toPure_1085_);
lean_inc_ref(v_toFunctor_1084_);
lean_inc(v_toBind_1083_);
lean_inc(v_t_x3f_1144_);
v___y_1138_ = v___x_1145_;
v___y_1139_ = v_t_x3f_1144_;
v___y_1140_ = v_d_x3f_1163_;
v___y_1141_ = v_t_x3f_1144_;
goto v___jp_1137_;
}
}
else
{
lean_inc(v_toPure_1085_);
lean_inc_ref(v_toFunctor_1084_);
lean_inc(v_toBind_1083_);
lean_inc(v_t_x3f_1144_);
v___y_1138_ = v___x_1145_;
v___y_1139_ = v_t_x3f_1144_;
v___y_1140_ = v_d_x3f_1163_;
v___y_1141_ = v_t_x3f_1144_;
goto v___jp_1137_;
}
}
}
else
{
lean_object* v___x_1180_; 
lean_inc(v_toPure_1085_);
lean_inc_ref(v_toFunctor_1084_);
lean_inc(v_toBind_1083_);
lean_dec(v___x_1146_);
v___x_1180_ = lean_box(0);
lean_inc(v_t_x3f_1144_);
v___y_1110_ = v___x_1145_;
v___y_1111_ = v_t_x3f_1144_;
v___y_1112_ = v_t_x3f_1144_;
v_d_x3f_1113_ = v___x_1180_;
goto v___jp_1109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* v_m_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_stx_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Elab_elabTerminationHints___redArg(v_inst_1203_, v_inst_1204_, v_stx_1205_);
return v___x_1206_;
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
