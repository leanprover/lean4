// Lean compiler output
// Module: Lean.Elab.DefView
// Imports: public import Lean.Elab.DeclNameGen public import Lean.Elab.DeclUtil
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedModifiers_default;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Elab_expandOptNamedPrio___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkInstanceName(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_instBEqComputeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instInhabitedSnapshotTree_default;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedDefKind_default;
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedDefKind;
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqDefKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqDefKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instBEqDefKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instBEqDefKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instBEqDefKind___closed__0 = (const lean_object*)&l_Lean_Elab_instBEqDefKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instBEqDefKind = (const lean_object*)&l_Lean_Elab_instBEqDefKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isTheorem___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isExample(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isExample___boxed(lean_object*);
static const lean_array_object l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0_value;
static const lean_string_object l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1 = (const lean_object*)&l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1_value;
static const lean_ctor_object l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2 = (const lean_object*)&l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2_value;
static lean_once_cell_t l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3;
static lean_once_cell_t l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedDefViewElabHeaderData_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedDefViewElabHeaderData;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(lean_object*);
static const lean_array_object l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value)} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1_value;
static const lean_string_object l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_ = (const lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value;
static const lean_string_object l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_ = (const lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value;
static const lean_string_object l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "DefsParsedSnapshot"};
static const lean_object* l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_ = (const lean_object*)&l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value;
static const lean_ctor_object l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_0),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_1),((lean_object*)&l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(203, 62, 250, 36, 153, 122, 46, 61)}};
static const lean_object* l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_ = (const lean_object*)&l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instImpl_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_ = (const lean_object*)&l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instTypeNameDefsParsedSnapshot = (const lean_object*)&l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1_value)}};
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7_value;
static const lean_ctor_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5_value)}};
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6_value)}};
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value)} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_value)} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_value)} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_value;
static lean_once_cell_t l_Lean_Elab_instInhabitedDefView_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedDefView_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedDefView_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedDefView;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 216, 85, 168, 141, 176, 253, 81)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_isInstance(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_isInstance___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_DefView_markDefEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "defeq"};
static const lean_object* l_Lean_Elab_DefView_markDefEq___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_DefView_markDefEq___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_DefView_markDefEq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_DefView_markDefEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 220, 195, 245, 59, 218, 252, 66)}};
static const lean_object* l_Lean_Elab_DefView_markDefEq___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_DefView_markDefEq___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_markDefEq___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_markDefEq___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_DefView_markDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_DefView_markDefEq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_DefView_markDefEq___closed__0 = (const lean_object*)&l_Lean_Elab_DefView_markDefEq___closed__0_value;
static const lean_ctor_object l_Lean_Elab_DefView_markDefEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_DefView_markDefEq___lam__0___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_DefView_markDefEq___closed__1 = (const lean_object*)&l_Lean_Elab_DefView_markDefEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_markDefEq(lean_object*);
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 166, 26, 13, 231, 61, 113)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3_value),LEAN_SCALAR_PTR_LITERAL(29, 67, 225, 118, 155, 2, 197, 97)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfDef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__0 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__1 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__2 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__3 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 1, 138, 227, 223, 112, 103, 179)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__4 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mkInstanceName"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__5 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 202, 238, 225, 213, 103, 187, 44)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(179, 135, 114, 115, 18, 204, 220, 213)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__6 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__7;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "generated "};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__8 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__9;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " for "};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__10 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Command_mkDefViewOfInstance___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "defaultOrOfNonempty"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8_value),LEAN_SCALAR_PTR_LITERAL(76, 19, 142, 204, 140, 85, 7, 204)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "default_or_ofNonempty%"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unsafe"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfExample___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7_value),((lean_object*)&l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0_value)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfExample___closed__0 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfExample___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_example"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfExample___closed__1 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfExample___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 8, 51, 7, 112, 171, 239, 122)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfExample___closed__2 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfExample___closed__3 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_isDefLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__0 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 116, 137, 74, 194, 103, 58, 54)}};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__1 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_isDefLike___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__2 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 217, 152, 21, 13, 97, 204, 102)}};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__3 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__4 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_isDefLike___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "example"};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__5 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__5_value),LEAN_SCALAR_PTR_LITERAL(108, 28, 224, 32, 144, 38, 51, 230)}};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__6 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_isDefLike___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "abbrev"};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__7 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__7_value),LEAN_SCALAR_PTR_LITERAL(34, 181, 25, 109, 89, 238, 86, 99)}};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__8 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_isDefLike___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__9 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__10 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__10_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Command_isDefLike(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Command_mkDefView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unexpected kind of definition"};
static const lean_object* l_Lean_Elab_Command_mkDefView___closed__0 = (const lean_object*)&l_Lean_Elab_Command_mkDefView___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Command_mkDefView___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkDefView___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__9_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "DefView"};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 122, 8, 89, 37, 107, 94, 7)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(34, 72, 191, 5, 97, 231, 115, 233)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(3, 151, 93, 82, 32, 95, 13, 197)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(53, 155, 219, 87, 227, 165, 44, 167)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 240, 120, 150, 30, 251, 20, 103)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 175, 96, 159, 50, 57, 89, 46)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 80, 179, 32, 181, 32, 199, 108)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(37, 248, 167, 23, 141, 24, 1, 218)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(19, 127, 79, 19, 22, 129, 157, 125)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 185, 236, 5, 38, 83, 111, 247)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1745620379) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(125, 189, 229, 213, 170, 230, 54, 74)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 120, 29, 149, 121, 223, 11, 7)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 164, 136, 80, 54, 134, 37, 108)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(139, 231, 231, 180, 118, 203, 197, 41)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
default: 
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
uint8_t v_x_boxed_9_; lean_object* v_res_10_; 
v_x_boxed_9_ = lean_unbox(v_x_8_);
v_res_10_ = l_Lean_Elab_DefKind_ctorIdx(v_x_boxed_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_toCtorIdx(uint8_t v_x_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Elab_DefKind_ctorIdx(v_x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_toCtorIdx___boxed(lean_object* v_x_13_){
_start:
{
uint8_t v_x_4__boxed_14_; lean_object* v_res_15_; 
v_x_4__boxed_14_ = lean_unbox(v_x_13_);
v_res_15_ = l_Lean_Elab_DefKind_toCtorIdx(v_x_4__boxed_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___redArg(lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___redArg___boxed(lean_object* v_k_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Elab_DefKind_ctorElim___redArg(v_k_17_);
lean_dec(v_k_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, uint8_t v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_inc(v_k_23_);
return v_k_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
uint8_t v_t_boxed_29_; lean_object* v_res_30_; 
v_t_boxed_29_ = lean_unbox(v_t_26_);
v_res_30_ = l_Lean_Elab_DefKind_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_boxed_29_, v_h_27_, v_k_28_);
lean_dec(v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___redArg(lean_object* v_def_31_){
_start:
{
lean_inc(v_def_31_);
return v_def_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___redArg___boxed(lean_object* v_def_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Elab_DefKind_def_elim___redArg(v_def_32_);
lean_dec(v_def_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim(lean_object* v_motive_34_, uint8_t v_t_35_, lean_object* v_h_36_, lean_object* v_def_37_){
_start:
{
lean_inc(v_def_37_);
return v_def_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___boxed(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_def_41_){
_start:
{
uint8_t v_t_boxed_42_; lean_object* v_res_43_; 
v_t_boxed_42_ = lean_unbox(v_t_39_);
v_res_43_ = l_Lean_Elab_DefKind_def_elim(v_motive_38_, v_t_boxed_42_, v_h_40_, v_def_41_);
lean_dec(v_def_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___redArg(lean_object* v_instance_44_){
_start:
{
lean_inc(v_instance_44_);
return v_instance_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___redArg___boxed(lean_object* v_instance_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Elab_DefKind_instance_elim___redArg(v_instance_45_);
lean_dec(v_instance_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim(lean_object* v_motive_47_, uint8_t v_t_48_, lean_object* v_h_49_, lean_object* v_instance_50_){
_start:
{
lean_inc(v_instance_50_);
return v_instance_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___boxed(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_instance_54_){
_start:
{
uint8_t v_t_boxed_55_; lean_object* v_res_56_; 
v_t_boxed_55_ = lean_unbox(v_t_52_);
v_res_56_ = l_Lean_Elab_DefKind_instance_elim(v_motive_51_, v_t_boxed_55_, v_h_53_, v_instance_54_);
lean_dec(v_instance_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___redArg(lean_object* v_theorem_57_){
_start:
{
lean_inc(v_theorem_57_);
return v_theorem_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___redArg___boxed(lean_object* v_theorem_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Elab_DefKind_theorem_elim___redArg(v_theorem_58_);
lean_dec(v_theorem_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim(lean_object* v_motive_60_, uint8_t v_t_61_, lean_object* v_h_62_, lean_object* v_theorem_63_){
_start:
{
lean_inc(v_theorem_63_);
return v_theorem_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___boxed(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_theorem_67_){
_start:
{
uint8_t v_t_boxed_68_; lean_object* v_res_69_; 
v_t_boxed_68_ = lean_unbox(v_t_65_);
v_res_69_ = l_Lean_Elab_DefKind_theorem_elim(v_motive_64_, v_t_boxed_68_, v_h_66_, v_theorem_67_);
lean_dec(v_theorem_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___redArg(lean_object* v_example_70_){
_start:
{
lean_inc(v_example_70_);
return v_example_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___redArg___boxed(lean_object* v_example_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Elab_DefKind_example_elim___redArg(v_example_71_);
lean_dec(v_example_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim(lean_object* v_motive_73_, uint8_t v_t_74_, lean_object* v_h_75_, lean_object* v_example_76_){
_start:
{
lean_inc(v_example_76_);
return v_example_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___boxed(lean_object* v_motive_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_example_80_){
_start:
{
uint8_t v_t_boxed_81_; lean_object* v_res_82_; 
v_t_boxed_81_ = lean_unbox(v_t_78_);
v_res_82_ = l_Lean_Elab_DefKind_example_elim(v_motive_77_, v_t_boxed_81_, v_h_79_, v_example_80_);
lean_dec(v_example_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___redArg(lean_object* v_opaque_83_){
_start:
{
lean_inc(v_opaque_83_);
return v_opaque_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___redArg___boxed(lean_object* v_opaque_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Elab_DefKind_opaque_elim___redArg(v_opaque_84_);
lean_dec(v_opaque_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim(lean_object* v_motive_86_, uint8_t v_t_87_, lean_object* v_h_88_, lean_object* v_opaque_89_){
_start:
{
lean_inc(v_opaque_89_);
return v_opaque_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___boxed(lean_object* v_motive_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_opaque_93_){
_start:
{
uint8_t v_t_boxed_94_; lean_object* v_res_95_; 
v_t_boxed_94_ = lean_unbox(v_t_91_);
v_res_95_ = l_Lean_Elab_DefKind_opaque_elim(v_motive_90_, v_t_boxed_94_, v_h_92_, v_opaque_93_);
lean_dec(v_opaque_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___redArg(lean_object* v_abbrev_96_){
_start:
{
lean_inc(v_abbrev_96_);
return v_abbrev_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___redArg___boxed(lean_object* v_abbrev_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Elab_DefKind_abbrev_elim___redArg(v_abbrev_97_);
lean_dec(v_abbrev_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim(lean_object* v_motive_99_, uint8_t v_t_100_, lean_object* v_h_101_, lean_object* v_abbrev_102_){
_start:
{
lean_inc(v_abbrev_102_);
return v_abbrev_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___boxed(lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_abbrev_106_){
_start:
{
uint8_t v_t_boxed_107_; lean_object* v_res_108_; 
v_t_boxed_107_ = lean_unbox(v_t_104_);
v_res_108_ = l_Lean_Elab_DefKind_abbrev_elim(v_motive_103_, v_t_boxed_107_, v_h_105_, v_abbrev_106_);
lean_dec(v_abbrev_106_);
return v_res_108_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedDefKind_default(void){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedDefKind(void){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqDefKind_beq(uint8_t v_x_111_, uint8_t v_y_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_113_ = l_Lean_Elab_DefKind_ctorIdx(v_x_111_);
v___x_114_ = l_Lean_Elab_DefKind_ctorIdx(v_y_112_);
v___x_115_ = lean_nat_dec_eq(v___x_113_, v___x_114_);
lean_dec(v___x_114_);
lean_dec(v___x_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqDefKind_beq___boxed(lean_object* v_x_116_, lean_object* v_y_117_){
_start:
{
uint8_t v_x_17__boxed_118_; uint8_t v_y_18__boxed_119_; uint8_t v_res_120_; lean_object* v_r_121_; 
v_x_17__boxed_118_ = lean_unbox(v_x_116_);
v_y_18__boxed_119_ = lean_unbox(v_y_117_);
v_res_120_ = l_Lean_Elab_instBEqDefKind_beq(v_x_17__boxed_118_, v_y_18__boxed_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t v_x_124_){
_start:
{
if (v_x_124_ == 2)
{
uint8_t v___x_125_; 
v___x_125_ = 1;
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isTheorem___boxed(lean_object* v_x_127_){
_start:
{
uint8_t v_x_21__boxed_128_; uint8_t v_res_129_; lean_object* v_r_130_; 
v_x_21__boxed_128_ = lean_unbox(v_x_127_);
v_res_129_ = l_Lean_Elab_DefKind_isTheorem(v_x_21__boxed_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isExample(uint8_t v_x_131_){
_start:
{
if (v_x_131_ == 3)
{
uint8_t v___x_132_; 
v___x_132_ = 1;
return v___x_132_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isExample___boxed(lean_object* v_x_134_){
_start:
{
uint8_t v_x_21__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_x_21__boxed_135_ = lean_unbox(v_x_134_);
v_res_136_ = l_Lean_Elab_DefKind_isExample(v_x_21__boxed_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_box(0);
v___x_144_ = ((lean_object*)(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2));
v___x_145_ = l_Lean_Expr_const___override(v___x_144_, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_146_ = lean_obj_once(&l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3, &l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3_once, _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = ((lean_object*)(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0));
v___x_149_ = lean_box(0);
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
lean_ctor_set(v___x_151_, 2, v___x_149_);
lean_ctor_set(v___x_151_, 3, v___x_148_);
lean_ctor_set(v___x_151_, 4, v___x_147_);
lean_ctor_set(v___x_151_, 5, v___x_146_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4, &l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4_once, _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData(void){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Elab_instInhabitedDefViewElabHeaderData_default;
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(lean_object* v_s_154_){
_start:
{
lean_object* v_toSnapshot_155_; lean_object* v_moreSnaps_156_; lean_object* v___x_157_; 
v_toSnapshot_155_ = lean_ctor_get(v_s_154_, 0);
v_moreSnaps_156_ = lean_ctor_get(v_s_154_, 3);
lean_inc_ref(v_moreSnaps_156_);
lean_inc_ref(v_toSnapshot_155_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_toSnapshot_155_);
lean_ctor_set(v___x_157_, 1, v_moreSnaps_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed(lean_object* v_s_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(v_s_158_);
lean_dec_ref(v_s_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_163_;
}
else
{
lean_object* v_val_164_; lean_object* v_toSnapshot_165_; lean_object* v_moreSnaps_166_; lean_object* v___x_167_; 
v_val_164_ = lean_ctor_get(v_x_162_, 0);
v_toSnapshot_165_ = lean_ctor_get(v_val_164_, 0);
v_moreSnaps_166_ = lean_ctor_get(v_val_164_, 3);
lean_inc_ref(v_moreSnaps_166_);
lean_inc_ref(v_toSnapshot_165_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v_toSnapshot_165_);
lean_ctor_set(v___x_167_, 1, v_moreSnaps_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(v_x_168_);
lean_dec(v_x_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1(lean_object* v___f_173_, lean_object* v_s_174_){
_start:
{
lean_object* v_toSnapshot_175_; lean_object* v_tacSnap_x3f_176_; lean_object* v_bodySnap_177_; lean_object* v_moreSnaps_178_; lean_object* v___y_180_; 
v_toSnapshot_175_ = lean_ctor_get(v_s_174_, 0);
lean_inc_ref(v_toSnapshot_175_);
v_tacSnap_x3f_176_ = lean_ctor_get(v_s_174_, 4);
lean_inc(v_tacSnap_x3f_176_);
v_bodySnap_177_ = lean_ctor_get(v_s_174_, 6);
lean_inc_ref(v_bodySnap_177_);
v_moreSnaps_178_ = lean_ctor_get(v_s_174_, 7);
lean_inc_ref(v_moreSnaps_178_);
lean_dec_ref(v_s_174_);
if (lean_obj_tag(v_tacSnap_x3f_176_) == 0)
{
lean_object* v___x_191_; 
v___x_191_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0));
v___y_180_ = v___x_191_;
goto v___jp_179_;
}
else
{
lean_object* v_val_192_; lean_object* v_stx_x3f_193_; lean_object* v_reportingRange_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_val_192_ = lean_ctor_get(v_tacSnap_x3f_176_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v_tacSnap_x3f_176_, 1);
v_stx_x3f_193_ = lean_ctor_get(v_val_192_, 0);
lean_inc(v_stx_x3f_193_);
v_reportingRange_194_ = lean_ctor_get(v_val_192_, 1);
lean_inc(v_reportingRange_194_);
v___x_195_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1));
v___x_196_ = 1;
v___x_197_ = l_Lean_Language_SnapshotTask_map___redArg(v_val_192_, v___x_195_, v_stx_x3f_193_, v_reportingRange_194_, v___x_196_);
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_mk_empty_array_with_capacity(v___x_198_);
v___x_200_ = lean_array_push(v___x_199_, v___x_197_);
v___y_180_ = v___x_200_;
goto v___jp_179_;
}
v___jp_179_:
{
lean_object* v_stx_x3f_181_; lean_object* v_reportingRange_182_; uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_stx_x3f_181_ = lean_ctor_get(v_bodySnap_177_, 0);
lean_inc(v_stx_x3f_181_);
v_reportingRange_182_ = lean_ctor_get(v_bodySnap_177_, 1);
lean_inc(v_reportingRange_182_);
v___x_183_ = 1;
v___x_184_ = l_Lean_Language_SnapshotTask_map___redArg(v_bodySnap_177_, v___f_173_, v_stx_x3f_181_, v_reportingRange_182_, v___x_183_);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_mk_empty_array_with_capacity(v___x_185_);
v___x_187_ = lean_array_push(v___x_186_, v___x_184_);
v___x_188_ = l_Array_append___redArg(v___y_180_, v___x_187_);
lean_dec_ref(v___x_187_);
v___x_189_ = l_Array_append___redArg(v___x_188_, v_moreSnaps_178_);
lean_dec_ref(v_moreSnaps_178_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_toSnapshot_175_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(lean_object* v___f_214_, lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v___x_216_; 
lean_dec_ref(v___f_214_);
v___x_216_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_216_;
}
else
{
lean_object* v_val_217_; lean_object* v_toSnapshot_218_; lean_object* v_tacSnap_x3f_219_; lean_object* v_bodySnap_220_; lean_object* v_moreSnaps_221_; lean_object* v___y_223_; 
v_val_217_ = lean_ctor_get(v_x_215_, 0);
lean_inc(v_val_217_);
lean_dec_ref_known(v_x_215_, 1);
v_toSnapshot_218_ = lean_ctor_get(v_val_217_, 0);
lean_inc_ref(v_toSnapshot_218_);
v_tacSnap_x3f_219_ = lean_ctor_get(v_val_217_, 4);
lean_inc(v_tacSnap_x3f_219_);
v_bodySnap_220_ = lean_ctor_get(v_val_217_, 6);
lean_inc_ref(v_bodySnap_220_);
v_moreSnaps_221_ = lean_ctor_get(v_val_217_, 7);
lean_inc_ref(v_moreSnaps_221_);
lean_dec(v_val_217_);
if (lean_obj_tag(v_tacSnap_x3f_219_) == 0)
{
lean_object* v___x_234_; 
v___x_234_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0));
v___y_223_ = v___x_234_;
goto v___jp_222_;
}
else
{
lean_object* v_val_235_; lean_object* v_stx_x3f_236_; lean_object* v_reportingRange_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_val_235_ = lean_ctor_get(v_tacSnap_x3f_219_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v_tacSnap_x3f_219_, 1);
v_stx_x3f_236_ = lean_ctor_get(v_val_235_, 0);
lean_inc(v_stx_x3f_236_);
v_reportingRange_237_ = lean_ctor_get(v_val_235_, 1);
lean_inc(v_reportingRange_237_);
v___x_238_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1));
v___x_239_ = 1;
v___x_240_ = l_Lean_Language_SnapshotTask_map___redArg(v_val_235_, v___x_238_, v_stx_x3f_236_, v_reportingRange_237_, v___x_239_);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_mk_empty_array_with_capacity(v___x_241_);
v___x_243_ = lean_array_push(v___x_242_, v___x_240_);
v___y_223_ = v___x_243_;
goto v___jp_222_;
}
v___jp_222_:
{
lean_object* v_stx_x3f_224_; lean_object* v_reportingRange_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_stx_x3f_224_ = lean_ctor_get(v_bodySnap_220_, 0);
lean_inc(v_stx_x3f_224_);
v_reportingRange_225_ = lean_ctor_get(v_bodySnap_220_, 1);
lean_inc(v_reportingRange_225_);
v___x_226_ = 1;
v___x_227_ = l_Lean_Language_SnapshotTask_map___redArg(v_bodySnap_220_, v___f_214_, v_stx_x3f_224_, v_reportingRange_225_, v___x_226_);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_mk_empty_array_with_capacity(v___x_228_);
v___x_230_ = lean_array_push(v___x_229_, v___x_227_);
v___x_231_ = l_Array_append___redArg(v___y_223_, v___x_230_);
lean_dec_ref(v___x_230_);
v___x_232_ = l_Array_append___redArg(v___x_231_, v_moreSnaps_221_);
lean_dec_ref(v_moreSnaps_221_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v_toSnapshot_218_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(lean_object* v___f_244_, lean_object* v_x_245_){
_start:
{
lean_object* v_headerProcessedSnap_246_; lean_object* v_stx_x3f_247_; lean_object* v_reportingRange_248_; uint8_t v___x_249_; lean_object* v___x_250_; 
v_headerProcessedSnap_246_ = lean_ctor_get(v_x_245_, 1);
lean_inc_ref(v_headerProcessedSnap_246_);
lean_dec_ref(v_x_245_);
v_stx_x3f_247_ = lean_ctor_get(v_headerProcessedSnap_246_, 0);
lean_inc(v_stx_x3f_247_);
v_reportingRange_248_ = lean_ctor_get(v_headerProcessedSnap_246_, 1);
lean_inc(v_reportingRange_248_);
v___x_249_ = 1;
v___x_250_ = l_Lean_Language_SnapshotTask_map___redArg(v_headerProcessedSnap_246_, v___f_244_, v_stx_x3f_247_, v_reportingRange_248_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2(lean_object* v___f_270_, lean_object* v_s_271_){
_start:
{
lean_object* v_toSnapshot_272_; lean_object* v_defs_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_284_; 
v_toSnapshot_272_ = lean_ctor_get(v_s_271_, 0);
v_defs_273_ = lean_ctor_get(v_s_271_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_s_271_);
if (v_isSharedCheck_284_ == 0)
{
v___x_275_ = v_s_271_;
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_defs_273_);
lean_inc(v_toSnapshot_272_);
lean_dec(v_s_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; size_t v_sz_278_; size_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_277_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9));
v_sz_278_ = lean_array_size(v_defs_273_);
v___x_279_ = ((size_t)0ULL);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_277_, v___f_270_, v_sz_278_, v___x_279_, v_defs_273_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v___x_280_);
v___x_282_ = v___x_275_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_toSnapshot_272_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView_default___closed__0(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; 
v___x_292_ = lean_box(0);
v___x_293_ = l_Lean_Elab_instInhabitedModifiers_default;
v___x_294_ = lean_box(0);
v___x_295_ = 0;
v___x_296_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_294_);
lean_ctor_set(v___x_296_, 2, v___x_293_);
lean_ctor_set(v___x_296_, 3, v___x_294_);
lean_ctor_set(v___x_296_, 4, v___x_294_);
lean_ctor_set(v___x_296_, 5, v___x_292_);
lean_ctor_set(v___x_296_, 6, v___x_294_);
lean_ctor_set(v___x_296_, 7, v___x_292_);
lean_ctor_set(v___x_296_, 8, v___x_292_);
lean_ctor_set(v___x_296_, 9, v___x_292_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*10, v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView_default(void){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Lean_Elab_instInhabitedDefView_default___closed__0, &l_Lean_Elab_instInhabitedDefView_default___closed__0_once, _init_l_Lean_Elab_instInhabitedDefView_default___closed__0);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView(void){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Elab_instInhabitedDefView_default;
return v___x_298_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(lean_object* v_as_302_, size_t v_i_303_, size_t v_stop_304_){
_start:
{
uint8_t v___x_305_; 
v___x_305_ = lean_usize_dec_eq(v_i_303_, v_stop_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v_name_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_306_ = lean_array_uget_borrowed(v_as_302_, v_i_303_);
v_name_307_ = lean_ctor_get(v___x_306_, 0);
v___x_308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1));
v___x_309_ = lean_name_eq(v_name_307_, v___x_308_);
if (v___x_309_ == 0)
{
size_t v___x_310_; size_t v___x_311_; 
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_add(v_i_303_, v___x_310_);
v_i_303_ = v___x_311_;
goto _start;
}
else
{
return v___x_309_;
}
}
else
{
uint8_t v___x_313_; 
v___x_313_ = 0;
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___boxed(lean_object* v_as_314_, lean_object* v_i_315_, lean_object* v_stop_316_){
_start:
{
size_t v_i_boxed_317_; size_t v_stop_boxed_318_; uint8_t v_res_319_; lean_object* v_r_320_; 
v_i_boxed_317_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_stop_boxed_318_ = lean_unbox_usize(v_stop_316_);
lean_dec(v_stop_316_);
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_as_314_, v_i_boxed_317_, v_stop_boxed_318_);
lean_dec_ref(v_as_314_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_isInstance(lean_object* v_view_321_){
_start:
{
lean_object* v_modifiers_322_; lean_object* v_attrs_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_modifiers_322_ = lean_ctor_get(v_view_321_, 2);
v_attrs_323_ = lean_ctor_get(v_modifiers_322_, 2);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_array_get_size(v_attrs_323_);
v___x_326_ = lean_nat_dec_lt(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
return v___x_326_;
}
else
{
if (v___x_326_ == 0)
{
return v___x_326_;
}
else
{
size_t v___x_327_; size_t v___x_328_; uint8_t v___x_329_; 
v___x_327_ = ((size_t)0ULL);
v___x_328_ = lean_usize_of_nat(v___x_325_);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_attrs_323_, v___x_327_, v___x_328_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_isInstance___boxed(lean_object* v_view_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Lean_Elab_DefView_isInstance(v_view_330_);
lean_dec_ref(v_view_330_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_markDefEq___lam__0(lean_object* v_x_336_){
_start:
{
lean_object* v_name_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_name_337_ = lean_ctor_get(v_x_336_, 0);
v___x_338_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___lam__0___closed__1));
v___x_339_ = lean_name_eq(v_name_337_, v___x_338_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = 1;
return v___x_340_;
}
else
{
uint8_t v___x_341_; 
v___x_341_ = 0;
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_markDefEq___lam__0___boxed(lean_object* v_x_342_){
_start:
{
uint8_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_Lean_Elab_DefView_markDefEq___lam__0(v_x_342_);
lean_dec_ref(v_x_342_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_markDefEq(lean_object* v_view_350_){
_start:
{
uint8_t v_kind_351_; lean_object* v_ref_352_; lean_object* v_headerRef_353_; lean_object* v_modifiers_354_; lean_object* v_declId_355_; lean_object* v_binders_356_; lean_object* v_type_x3f_357_; lean_object* v_value_358_; lean_object* v_docString_x3f_359_; lean_object* v_headerSnap_x3f_360_; lean_object* v_deriving_x3f_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_372_; 
v_kind_351_ = lean_ctor_get_uint8(v_view_350_, sizeof(void*)*10);
v_ref_352_ = lean_ctor_get(v_view_350_, 0);
v_headerRef_353_ = lean_ctor_get(v_view_350_, 1);
v_modifiers_354_ = lean_ctor_get(v_view_350_, 2);
v_declId_355_ = lean_ctor_get(v_view_350_, 3);
v_binders_356_ = lean_ctor_get(v_view_350_, 4);
v_type_x3f_357_ = lean_ctor_get(v_view_350_, 5);
v_value_358_ = lean_ctor_get(v_view_350_, 6);
v_docString_x3f_359_ = lean_ctor_get(v_view_350_, 7);
v_headerSnap_x3f_360_ = lean_ctor_get(v_view_350_, 8);
v_deriving_x3f_361_ = lean_ctor_get(v_view_350_, 9);
v_isSharedCheck_372_ = !lean_is_exclusive(v_view_350_);
if (v_isSharedCheck_372_ == 0)
{
v___x_363_ = v_view_350_;
v_isShared_364_ = v_isSharedCheck_372_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_deriving_x3f_361_);
lean_inc(v_headerSnap_x3f_360_);
lean_inc(v_docString_x3f_359_);
lean_inc(v_value_358_);
lean_inc(v_type_x3f_357_);
lean_inc(v_binders_356_);
lean_inc(v_declId_355_);
lean_inc(v_modifiers_354_);
lean_inc(v_headerRef_353_);
lean_inc(v_ref_352_);
lean_dec(v_view_350_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_372_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___f_365_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___closed__0));
v___x_366_ = l_Lean_Elab_Modifiers_filterAttrs(v_modifiers_354_, v___f_365_);
v___x_367_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___closed__1));
v___x_368_ = l_Lean_Elab_Modifiers_addFirstAttr(v___x_366_, v___x_367_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 2, v___x_368_);
v___x_370_ = v___x_363_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_ref_352_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_headerRef_353_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v_declId_355_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v_binders_356_);
lean_ctor_set(v_reuseFailAlloc_371_, 5, v_type_x3f_357_);
lean_ctor_set(v_reuseFailAlloc_371_, 6, v_value_358_);
lean_ctor_set(v_reuseFailAlloc_371_, 7, v_docString_x3f_359_);
lean_ctor_set(v_reuseFailAlloc_371_, 8, v_headerSnap_x3f_360_);
lean_ctor_set(v_reuseFailAlloc_371_, 9, v_deriving_x3f_361_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*10, v_kind_351_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev(lean_object* v_modifiers_390_, lean_object* v_stx_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_fst_395_; lean_object* v_snd_396_; lean_object* v___x_397_; lean_object* v_modifiers_398_; lean_object* v___x_399_; lean_object* v_modifiers_400_; lean_object* v_docString_x3f_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_392_ = lean_unsigned_to_nat(2u);
v___x_393_ = l_Lean_Syntax_getArg(v_stx_391_, v___x_392_);
v___x_394_ = l_Lean_Elab_expandOptDeclSig(v___x_393_);
lean_dec(v___x_393_);
v_fst_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_fst_395_);
v_snd_396_ = lean_ctor_get(v___x_394_, 1);
lean_inc(v_snd_396_);
lean_dec_ref(v___x_394_);
v___x_397_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2));
v_modifiers_398_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_390_, v___x_397_);
v___x_399_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5));
v_modifiers_400_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_398_, v___x_399_);
v_docString_x3f_401_ = lean_ctor_get(v_modifiers_400_, 1);
lean_inc(v_docString_x3f_401_);
v___x_402_ = 5;
v___x_403_ = l_Lean_Syntax_getArgs(v_stx_391_);
v___x_404_ = lean_unsigned_to_nat(3u);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = l_Array_toSubarray___redArg(v___x_403_, v___x_405_, v___x_404_);
v___x_407_ = l_Subarray_copy___redArg(v___x_406_);
v___x_408_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_409_ = lean_box(2);
v___x_410_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_407_);
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = l_Lean_Syntax_getArg(v_stx_391_, v___x_411_);
v___x_413_ = l_Lean_Syntax_getArg(v_stx_391_, v___x_404_);
v___x_414_ = lean_box(0);
v___x_415_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_415_, 0, v_stx_391_);
lean_ctor_set(v___x_415_, 1, v___x_410_);
lean_ctor_set(v___x_415_, 2, v_modifiers_400_);
lean_ctor_set(v___x_415_, 3, v___x_412_);
lean_ctor_set(v___x_415_, 4, v_fst_395_);
lean_ctor_set(v___x_415_, 5, v_snd_396_);
lean_ctor_set(v___x_415_, 6, v___x_413_);
lean_ctor_set(v___x_415_, 7, v_docString_x3f_401_);
lean_ctor_set(v___x_415_, 8, v___x_414_);
lean_ctor_set(v___x_415_, 9, v___x_414_);
lean_ctor_set_uint8(v___x_415_, sizeof(void*)*10, v___x_402_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfDef(lean_object* v_modifiers_416_, lean_object* v_stx_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_fst_421_; lean_object* v_snd_422_; lean_object* v___y_424_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_418_ = lean_unsigned_to_nat(2u);
v___x_419_ = l_Lean_Syntax_getArg(v_stx_417_, v___x_418_);
v___x_420_ = l_Lean_Elab_expandOptDeclSig(v___x_419_);
lean_dec(v___x_419_);
v_fst_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_fst_421_);
v_snd_422_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_snd_422_);
lean_dec_ref(v___x_420_);
v___x_440_ = lean_unsigned_to_nat(4u);
v___x_441_ = l_Lean_Syntax_getArg(v_stx_417_, v___x_440_);
v___x_442_ = l_Lean_Syntax_isNone(v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = l_Lean_Syntax_getArg(v___x_441_, v___x_443_);
lean_dec(v___x_441_);
v___x_445_ = l_Lean_Syntax_getSepArgs(v___x_444_);
lean_dec(v___x_444_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
v___y_424_ = v___x_446_;
goto v___jp_423_;
}
else
{
lean_object* v___x_447_; 
lean_dec(v___x_441_);
v___x_447_ = lean_box(0);
v___y_424_ = v___x_447_;
goto v___jp_423_;
}
v___jp_423_:
{
lean_object* v_docString_x3f_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_docString_x3f_425_ = lean_ctor_get(v_modifiers_416_, 1);
lean_inc(v_docString_x3f_425_);
v___x_426_ = 0;
v___x_427_ = l_Lean_Syntax_getArgs(v_stx_417_);
v___x_428_ = lean_unsigned_to_nat(3u);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = l_Array_toSubarray___redArg(v___x_427_, v___x_429_, v___x_428_);
v___x_431_ = l_Subarray_copy___redArg(v___x_430_);
v___x_432_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_433_ = lean_box(2);
v___x_434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
lean_ctor_set(v___x_434_, 2, v___x_431_);
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = l_Lean_Syntax_getArg(v_stx_417_, v___x_435_);
v___x_437_ = l_Lean_Syntax_getArg(v_stx_417_, v___x_428_);
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_439_, 0, v_stx_417_);
lean_ctor_set(v___x_439_, 1, v___x_434_);
lean_ctor_set(v___x_439_, 2, v_modifiers_416_);
lean_ctor_set(v___x_439_, 3, v___x_436_);
lean_ctor_set(v___x_439_, 4, v_fst_421_);
lean_ctor_set(v___x_439_, 5, v_snd_422_);
lean_ctor_set(v___x_439_, 6, v___x_437_);
lean_ctor_set(v___x_439_, 7, v_docString_x3f_425_);
lean_ctor_set(v___x_439_, 8, v___x_438_);
lean_ctor_set(v___x_439_, 9, v___y_424_);
lean_ctor_set_uint8(v___x_439_, sizeof(void*)*10, v___x_426_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem(lean_object* v_modifiers_448_, lean_object* v_stx_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v_fst_453_; lean_object* v_snd_454_; lean_object* v_docString_x3f_455_; uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_450_ = lean_unsigned_to_nat(2u);
v___x_451_ = l_Lean_Syntax_getArg(v_stx_449_, v___x_450_);
v___x_452_ = l_Lean_Elab_expandDeclSig(v___x_451_);
lean_dec(v___x_451_);
v_fst_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_fst_453_);
v_snd_454_ = lean_ctor_get(v___x_452_, 1);
lean_inc(v_snd_454_);
lean_dec_ref(v___x_452_);
v_docString_x3f_455_ = lean_ctor_get(v_modifiers_448_, 1);
lean_inc(v_docString_x3f_455_);
v___x_456_ = 2;
v___x_457_ = l_Lean_Syntax_getArgs(v_stx_449_);
v___x_458_ = lean_unsigned_to_nat(3u);
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = l_Array_toSubarray___redArg(v___x_457_, v___x_459_, v___x_458_);
v___x_461_ = l_Subarray_copy___redArg(v___x_460_);
v___x_462_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_463_ = lean_box(2);
v___x_464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_462_);
lean_ctor_set(v___x_464_, 2, v___x_461_);
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = l_Lean_Syntax_getArg(v_stx_449_, v___x_465_);
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v_snd_454_);
v___x_468_ = l_Lean_Syntax_getArg(v_stx_449_, v___x_458_);
v___x_469_ = lean_box(0);
v___x_470_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_470_, 0, v_stx_449_);
lean_ctor_set(v___x_470_, 1, v___x_464_);
lean_ctor_set(v___x_470_, 2, v_modifiers_448_);
lean_ctor_set(v___x_470_, 3, v___x_466_);
lean_ctor_set(v___x_470_, 4, v_fst_453_);
lean_ctor_set(v___x_470_, 5, v___x_467_);
lean_ctor_set(v___x_470_, 6, v___x_468_);
lean_ctor_set(v___x_470_, 7, v_docString_x3f_455_);
lean_ctor_set(v___x_470_, 8, v___x_469_);
lean_ctor_set(v___x_470_, 9, v___x_469_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*10, v___x_456_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; lean_object* v_env_474_; lean_object* v___x_475_; lean_object* v_mainModule_476_; lean_object* v___x_477_; 
v___x_473_ = lean_st_ref_get(v___y_471_);
v_env_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc_ref(v_env_474_);
lean_dec(v___x_473_);
v___x_475_ = l_Lean_Environment_header(v_env_474_);
lean_dec_ref(v_env_474_);
v_mainModule_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_mainModule_476_);
lean_dec_ref(v___x_475_);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v_mainModule_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg___boxed(lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_478_);
lean_dec(v___y_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___boxed(lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_488_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = l_Lean_maxRecDepthErrorMessage;
v___x_495_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3);
v___x_497_ = l_Lean_MessageData_ofFormat(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4);
v___x_499_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2));
v___x_500_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___x_498_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(lean_object* v_ref_501_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_ref_501_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___boxed(lean_object* v_ref_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(lean_object* v_x_509_, lean_object* v___y_510_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; 
v_a_511_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_a_511_);
v___x_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_512_, 0, v_a_511_);
lean_ctor_set(v___x_512_, 1, v___y_510_);
return v___x_512_;
}
else
{
lean_object* v_a_513_; lean_object* v___x_514_; 
v_a_513_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_a_513_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v_a_513_);
lean_ctor_set(v___x_514_, 1, v___y_510_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg___boxed(lean_object* v_x_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_515_, v___y_516_);
lean_dec_ref(v_x_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(lean_object* v_env_518_, lean_object* v_stx_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_518_, v_stx_519_, v___y_520_, v___y_521_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
if (lean_obj_tag(v_a_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
v_a_524_ = lean_ctor_get(v___x_522_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v___x_522_, 0);
lean_dec(v_unused_533_);
v___x_526_ = v___x_522_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_522_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_box(0);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_a_524_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
else
{
lean_object* v_val_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_562_; 
v_val_534_ = lean_ctor_get(v_a_523_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_a_523_);
if (v_isSharedCheck_562_ == 0)
{
v___x_536_ = v_a_523_;
v_isShared_537_ = v_isSharedCheck_562_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_val_534_);
lean_dec(v_a_523_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_562_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_snd_538_; 
v_snd_538_ = lean_ctor_get(v_val_534_, 1);
lean_inc(v_snd_538_);
lean_dec(v_val_534_);
if (lean_obj_tag(v_snd_538_) == 0)
{
lean_object* v_a_539_; lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_548_; 
lean_del_object(v___x_536_);
v_a_539_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_522_, 2);
v_a_540_ = lean_ctor_get(v_snd_538_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_snd_538_);
if (v_isSharedCheck_548_ == 0)
{
v___x_542_ = v_snd_538_;
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v_snd_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_547_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; 
v___x_546_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_545_, v_a_539_);
lean_dec_ref(v___x_545_);
return v___x_546_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_561_; 
v_a_549_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_522_, 2);
v_a_550_ = lean_ctor_get(v_snd_538_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v_snd_538_);
if (v_isSharedCheck_561_ == 0)
{
v___x_552_ = v_snd_538_;
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v_snd_538_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v_a_550_);
v___x_555_ = v___x_536_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_560_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_557_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_555_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_559_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; 
v___x_558_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_557_, v_a_549_);
lean_dec_ref(v___x_557_);
return v___x_558_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_563_ = lean_ctor_get(v___x_522_, 0);
v_a_564_ = lean_ctor_get(v___x_522_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_522_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_inc(v_a_563_);
lean_dec(v___x_522_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_563_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed(lean_object* v_env_572_, lean_object* v_stx_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(v_env_572_, v_stx_573_, v___y_574_, v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(lean_object* v_env_577_, lean_object* v_currNamespace_578_, lean_object* v_openDecls_579_, lean_object* v_n_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = l_Lean_ResolveName_resolveNamespace(v_env_577_, v_currNamespace_578_, v_openDecls_579_, v_n_580_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___y_582_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed(lean_object* v_env_585_, lean_object* v_currNamespace_586_, lean_object* v_openDecls_587_, lean_object* v_n_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(v_env_585_, v_currNamespace_586_, v_openDecls_587_, v_n_588_, v___y_589_, v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(lean_object* v_currNamespace_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v_currNamespace_592_);
lean_ctor_set(v___x_595_, 1, v___y_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(v_currNamespace_596_, v___y_597_, v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_599_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
v___x_601_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg(){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0);
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___boxed(lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v_res_607_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_608_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
lean_ctor_set(v___x_613_, 2, v___x_612_);
lean_ctor_set(v___x_613_, 3, v___x_612_);
lean_ctor_set(v___x_613_, 4, v___x_611_);
lean_ctor_set(v___x_613_, 5, v___x_611_);
lean_ctor_set(v___x_613_, 6, v___x_611_);
lean_ctor_set(v___x_613_, 7, v___x_611_);
lean_ctor_set(v___x_613_, 8, v___x_611_);
lean_ctor_set(v___x_613_, 9, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_unsigned_to_nat(32u);
v___x_615_ = lean_mk_empty_array_with_capacity(v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_617_ = ((size_t)5ULL);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_unsigned_to_nat(32u);
v___x_620_ = lean_mk_empty_array_with_capacity(v___x_619_);
v___x_621_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3);
v___x_622_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v___x_620_);
lean_ctor_set(v___x_622_, 2, v___x_618_);
lean_ctor_set(v___x_622_, 3, v___x_618_);
lean_ctor_set_usize(v___x_622_, 4, v___x_617_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_box(1);
v___x_624_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4);
v___x_625_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
v___x_626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
lean_ctor_set(v___x_626_, 2, v___x_623_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(lean_object* v_msgData_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; lean_object* v_env_631_; lean_object* v___x_632_; lean_object* v_scopes_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_opts_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_630_ = lean_st_ref_get(v___y_628_);
v_env_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc_ref(v_env_631_);
lean_dec(v___x_630_);
v___x_632_ = lean_st_ref_get(v___y_628_);
v_scopes_633_ = lean_ctor_get(v___x_632_, 2);
lean_inc(v_scopes_633_);
lean_dec(v___x_632_);
v___x_634_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_635_ = l_List_head_x21___redArg(v___x_634_, v_scopes_633_);
lean_dec(v_scopes_633_);
v_opts_636_ = lean_ctor_get(v___x_635_, 1);
lean_inc_ref(v_opts_636_);
lean_dec(v___x_635_);
v___x_637_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2);
v___x_638_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5);
v___x_639_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_639_, 0, v_env_631_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_638_);
lean_ctor_set(v___x_639_, 3, v_opts_636_);
v___x_640_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v_msgData_627_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___boxed(lean_object* v_msgData_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_642_, v___y_643_);
lean_dec(v___y_643_);
return v_res_645_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0(void){
_start:
{
lean_object* v___x_646_; double v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = lean_float_of_nat(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(lean_object* v_cls_651_, lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Elab_Command_getRef___redArg(v___y_653_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_658_; lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_705_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_652_, v___y_654_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_705_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_705_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_705_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v_traceState_664_; lean_object* v_env_665_; lean_object* v_messages_666_; lean_object* v_scopes_667_; lean_object* v_usedQuotCtxts_668_; lean_object* v_nextMacroScope_669_; lean_object* v_maxRecDepth_670_; lean_object* v_ngen_671_; lean_object* v_auxDeclNGen_672_; lean_object* v_infoState_673_; lean_object* v_snapshotTasks_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_704_; 
v___x_663_ = lean_st_ref_take(v___y_654_);
v_traceState_664_ = lean_ctor_get(v___x_663_, 9);
v_env_665_ = lean_ctor_get(v___x_663_, 0);
v_messages_666_ = lean_ctor_get(v___x_663_, 1);
v_scopes_667_ = lean_ctor_get(v___x_663_, 2);
v_usedQuotCtxts_668_ = lean_ctor_get(v___x_663_, 3);
v_nextMacroScope_669_ = lean_ctor_get(v___x_663_, 4);
v_maxRecDepth_670_ = lean_ctor_get(v___x_663_, 5);
v_ngen_671_ = lean_ctor_get(v___x_663_, 6);
v_auxDeclNGen_672_ = lean_ctor_get(v___x_663_, 7);
v_infoState_673_ = lean_ctor_get(v___x_663_, 8);
v_snapshotTasks_674_ = lean_ctor_get(v___x_663_, 10);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_704_ == 0)
{
v___x_676_ = v___x_663_;
v_isShared_677_ = v_isSharedCheck_704_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_snapshotTasks_674_);
lean_inc(v_traceState_664_);
lean_inc(v_infoState_673_);
lean_inc(v_auxDeclNGen_672_);
lean_inc(v_ngen_671_);
lean_inc(v_maxRecDepth_670_);
lean_inc(v_nextMacroScope_669_);
lean_inc(v_usedQuotCtxts_668_);
lean_inc(v_scopes_667_);
lean_inc(v_messages_666_);
lean_inc(v_env_665_);
lean_dec(v___x_663_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_704_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
uint64_t v_tid_678_; lean_object* v_traces_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_703_; 
v_tid_678_ = lean_ctor_get_uint64(v_traceState_664_, sizeof(void*)*1);
v_traces_679_ = lean_ctor_get(v_traceState_664_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v_traceState_664_);
if (v_isSharedCheck_703_ == 0)
{
v___x_681_ = v_traceState_664_;
v_isShared_682_ = v_isSharedCheck_703_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_traces_679_);
lean_dec(v_traceState_664_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_703_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; double v___x_684_; uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_683_ = lean_box(0);
v___x_684_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0);
v___x_685_ = 0;
v___x_686_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1));
v___x_687_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_687_, 0, v_cls_651_);
lean_ctor_set(v___x_687_, 1, v___x_683_);
lean_ctor_set(v___x_687_, 2, v___x_686_);
lean_ctor_set_float(v___x_687_, sizeof(void*)*3, v___x_684_);
lean_ctor_set_float(v___x_687_, sizeof(void*)*3 + 8, v___x_684_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*3 + 16, v___x_685_);
v___x_688_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2));
v___x_689_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v_a_659_);
lean_ctor_set(v___x_689_, 2, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_a_657_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_Lean_PersistentArray_push___redArg(v_traces_679_, v___x_690_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_691_);
v___x_693_ = v___x_681_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_691_);
lean_ctor_set_uint64(v_reuseFailAlloc_702_, sizeof(void*)*1, v_tid_678_);
v___x_693_ = v_reuseFailAlloc_702_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 9, v___x_693_);
v___x_695_ = v___x_676_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_env_665_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_messages_666_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_scopes_667_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_usedQuotCtxts_668_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_nextMacroScope_669_);
lean_ctor_set(v_reuseFailAlloc_701_, 5, v_maxRecDepth_670_);
lean_ctor_set(v_reuseFailAlloc_701_, 6, v_ngen_671_);
lean_ctor_set(v_reuseFailAlloc_701_, 7, v_auxDeclNGen_672_);
lean_ctor_set(v_reuseFailAlloc_701_, 8, v_infoState_673_);
lean_ctor_set(v_reuseFailAlloc_701_, 9, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_701_, 10, v_snapshotTasks_674_);
v___x_695_ = v_reuseFailAlloc_701_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_696_ = lean_st_ref_set(v___y_654_, v___x_695_);
v___x_697_ = lean_box(0);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_697_);
v___x_699_ = v___x_661_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v_msg_652_);
lean_dec(v_cls_651_);
v_a_706_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_656_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_656_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___boxed(lean_object* v_cls_714_, lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_cls_714_, v_msg_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_719_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(lean_object* v_keys_720_, lean_object* v_i_721_, lean_object* v_k_722_){
_start:
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = lean_array_get_size(v_keys_720_);
v___x_724_ = lean_nat_dec_lt(v_i_721_, v___x_723_);
if (v___x_724_ == 0)
{
lean_dec(v_i_721_);
return v___x_724_;
}
else
{
lean_object* v_k_x27_725_; uint8_t v___x_726_; 
v_k_x27_725_ = lean_array_fget_borrowed(v_keys_720_, v_i_721_);
v___x_726_ = l_Lean_instBEqExtraModUse_beq(v_k_722_, v_k_x27_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_add(v_i_721_, v___x_727_);
lean_dec(v_i_721_);
v_i_721_ = v___x_728_;
goto _start;
}
else
{
lean_dec(v_i_721_);
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg___boxed(lean_object* v_keys_730_, lean_object* v_i_731_, lean_object* v_k_732_){
_start:
{
uint8_t v_res_733_; lean_object* v_r_734_; 
v_res_733_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_730_, v_i_731_, v_k_732_);
lean_dec_ref(v_k_732_);
lean_dec_ref(v_keys_730_);
v_r_734_ = lean_box(v_res_733_);
return v_r_734_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(lean_object* v_x_735_, size_t v_x_736_, lean_object* v_x_737_){
_start:
{
if (lean_obj_tag(v_x_735_) == 0)
{
lean_object* v_es_738_; lean_object* v___x_739_; size_t v___x_740_; size_t v___x_741_; lean_object* v_j_742_; lean_object* v___x_743_; 
v_es_738_ = lean_ctor_get(v_x_735_, 0);
v___x_739_ = lean_box(2);
v___x_740_ = ((size_t)31ULL);
v___x_741_ = lean_usize_land(v_x_736_, v___x_740_);
v_j_742_ = lean_usize_to_nat(v___x_741_);
v___x_743_ = lean_array_get_borrowed(v___x_739_, v_es_738_, v_j_742_);
lean_dec(v_j_742_);
switch(lean_obj_tag(v___x_743_))
{
case 0:
{
lean_object* v_key_744_; uint8_t v___x_745_; 
v_key_744_ = lean_ctor_get(v___x_743_, 0);
v___x_745_ = l_Lean_instBEqExtraModUse_beq(v_x_737_, v_key_744_);
return v___x_745_;
}
case 1:
{
lean_object* v_node_746_; size_t v___x_747_; size_t v___x_748_; 
v_node_746_ = lean_ctor_get(v___x_743_, 0);
v___x_747_ = ((size_t)5ULL);
v___x_748_ = lean_usize_shift_right(v_x_736_, v___x_747_);
v_x_735_ = v_node_746_;
v_x_736_ = v___x_748_;
goto _start;
}
default: 
{
uint8_t v___x_750_; 
v___x_750_ = 0;
return v___x_750_;
}
}
}
else
{
lean_object* v_ks_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_ks_751_ = lean_ctor_get(v_x_735_, 0);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_ks_751_, v___x_752_, v_x_737_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
size_t v_x_16971__boxed_757_; uint8_t v_res_758_; lean_object* v_r_759_; 
v_x_16971__boxed_757_ = lean_unbox_usize(v_x_755_);
lean_dec(v_x_755_);
v_res_758_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_754_, v_x_16971__boxed_757_, v_x_756_);
lean_dec_ref(v_x_756_);
lean_dec_ref(v_x_754_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
uint64_t v___x_762_; size_t v___x_763_; uint8_t v___x_764_; 
v___x_762_ = l_Lean_instHashableExtraModUse_hash(v_x_761_);
v___x_763_ = lean_uint64_to_usize(v___x_762_);
v___x_764_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_760_, v___x_763_, v_x_761_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_765_, v_x_766_);
lean_dec_ref(v_x_766_);
lean_dec_ref(v_x_765_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1));
v___x_772_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0));
v___x_773_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_772_, v___x_771_);
return v___x_773_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7));
v___x_782_ = l_Lean_stringToMessageData(v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_cls_788_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4));
v___x_789_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11));
v___x_790_ = l_Lean_Name_append(v___x_789_, v_cls_788_);
return v___x_790_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(lean_object* v_mod_801_, uint8_t v_isMeta_802_, lean_object* v_hint_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; lean_object* v_env_808_; uint8_t v_isExporting_809_; lean_object* v___x_810_; lean_object* v_env_811_; lean_object* v___x_812_; lean_object* v_entry_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___y_818_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_807_ = lean_st_ref_get(v___y_805_);
v_env_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc_ref(v_env_808_);
lean_dec(v___x_807_);
v_isExporting_809_ = lean_ctor_get_uint8(v_env_808_, sizeof(void*)*8);
lean_dec_ref(v_env_808_);
v___x_810_ = lean_st_ref_get(v___y_805_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref(v_env_811_);
lean_dec(v___x_810_);
v___x_812_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2);
lean_inc(v_mod_801_);
v_entry_813_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_813_, 0, v_mod_801_);
lean_ctor_set_uint8(v_entry_813_, sizeof(void*)*1, v_isExporting_809_);
lean_ctor_set_uint8(v_entry_813_, sizeof(void*)*1 + 1, v_isMeta_802_);
v___x_814_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_815_ = lean_box(1);
v___x_816_ = lean_box(0);
v___x_844_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_812_, v___x_814_, v_env_811_, v___x_815_, v___x_816_);
v___x_845_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v___x_844_, v_entry_813_);
lean_dec(v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_scopes_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v_opts_852_; uint8_t v_hasTrace_853_; 
v___x_846_ = l_Lean_inheritedTraceOptions;
v___x_847_ = lean_st_ref_get(v___x_846_);
v___x_848_ = lean_st_ref_get(v___y_805_);
v_scopes_849_ = lean_ctor_get(v___x_848_, 2);
lean_inc(v_scopes_849_);
lean_dec(v___x_848_);
v___x_850_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_851_ = l_List_head_x21___redArg(v___x_850_, v_scopes_849_);
lean_dec(v_scopes_849_);
v_opts_852_ = lean_ctor_get(v___x_851_, 1);
lean_inc_ref(v_opts_852_);
lean_dec(v___x_851_);
v_hasTrace_853_ = lean_ctor_get_uint8(v_opts_852_, sizeof(void*)*1);
if (v_hasTrace_853_ == 0)
{
lean_dec_ref(v_opts_852_);
lean_dec(v___x_847_);
lean_dec(v_hint_803_);
lean_dec(v_mod_801_);
v___y_818_ = v___y_805_;
goto v___jp_817_;
}
else
{
lean_object* v_cls_854_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_cls_854_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4));
v___x_874_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12);
v___x_875_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_847_, v_opts_852_, v___x_874_);
lean_dec_ref(v_opts_852_);
lean_dec(v___x_847_);
if (v___x_875_ == 0)
{
lean_dec(v_hint_803_);
lean_dec(v_mod_801_);
v___y_818_ = v___y_805_;
goto v___jp_817_;
}
else
{
lean_object* v___x_876_; lean_object* v___y_878_; 
v___x_876_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14);
if (v_isExporting_809_ == 0)
{
lean_object* v___x_885_; 
v___x_885_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19));
v___y_878_ = v___x_885_;
goto v___jp_877_;
}
else
{
lean_object* v___x_886_; 
v___x_886_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20));
v___y_878_ = v___x_886_;
goto v___jp_877_;
}
v___jp_877_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_inc_ref(v___y_878_);
v___x_879_ = l_Lean_stringToMessageData(v___y_878_);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_876_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
if (v_isMeta_802_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17));
v___y_861_ = v___x_882_;
v___y_862_ = v___x_883_;
goto v___jp_860_;
}
else
{
lean_object* v___x_884_; 
v___x_884_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18));
v___y_861_ = v___x_882_;
v___y_862_ = v___x_884_;
goto v___jp_860_;
}
}
}
v___jp_855_:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___y_856_);
lean_ctor_set(v___x_858_, 1, v___y_857_);
v___x_859_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_cls_854_, v___x_858_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_dec_ref_known(v___x_859_, 1);
v___y_818_ = v___y_805_;
goto v___jp_817_;
}
else
{
lean_dec_ref_known(v_entry_813_, 1);
return v___x_859_;
}
}
v___jp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
lean_inc_ref(v___y_862_);
v___x_863_ = l_Lean_stringToMessageData(v___y_862_);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___y_861_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_Lean_MessageData_ofName(v_mod_801_);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_Name_isAnonymous(v_hint_803_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8);
v___x_871_ = l_Lean_MessageData_ofName(v_hint_803_);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___y_856_ = v___x_868_;
v___y_857_ = v___x_872_;
goto v___jp_855_;
}
else
{
lean_object* v___x_873_; 
lean_dec(v_hint_803_);
v___x_873_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9);
v___y_856_ = v___x_868_;
v___y_857_ = v___x_873_;
goto v___jp_855_;
}
}
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec_ref_known(v_entry_813_, 1);
lean_dec(v_hint_803_);
lean_dec(v_mod_801_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
v___jp_817_:
{
lean_object* v___x_819_; lean_object* v_toEnvExtension_820_; lean_object* v_env_821_; lean_object* v_messages_822_; lean_object* v_scopes_823_; lean_object* v_usedQuotCtxts_824_; lean_object* v_nextMacroScope_825_; lean_object* v_maxRecDepth_826_; lean_object* v_ngen_827_; lean_object* v_auxDeclNGen_828_; lean_object* v_infoState_829_; lean_object* v_traceState_830_; lean_object* v_snapshotTasks_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_843_; 
v___x_819_ = lean_st_ref_take(v___y_818_);
v_toEnvExtension_820_ = lean_ctor_get(v___x_814_, 0);
v_env_821_ = lean_ctor_get(v___x_819_, 0);
v_messages_822_ = lean_ctor_get(v___x_819_, 1);
v_scopes_823_ = lean_ctor_get(v___x_819_, 2);
v_usedQuotCtxts_824_ = lean_ctor_get(v___x_819_, 3);
v_nextMacroScope_825_ = lean_ctor_get(v___x_819_, 4);
v_maxRecDepth_826_ = lean_ctor_get(v___x_819_, 5);
v_ngen_827_ = lean_ctor_get(v___x_819_, 6);
v_auxDeclNGen_828_ = lean_ctor_get(v___x_819_, 7);
v_infoState_829_ = lean_ctor_get(v___x_819_, 8);
v_traceState_830_ = lean_ctor_get(v___x_819_, 9);
v_snapshotTasks_831_ = lean_ctor_get(v___x_819_, 10);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_843_ == 0)
{
v___x_833_ = v___x_819_;
v_isShared_834_ = v_isSharedCheck_843_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_snapshotTasks_831_);
lean_inc(v_traceState_830_);
lean_inc(v_infoState_829_);
lean_inc(v_auxDeclNGen_828_);
lean_inc(v_ngen_827_);
lean_inc(v_maxRecDepth_826_);
lean_inc(v_nextMacroScope_825_);
lean_inc(v_usedQuotCtxts_824_);
lean_inc(v_scopes_823_);
lean_inc(v_messages_822_);
lean_inc(v_env_821_);
lean_dec(v___x_819_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_843_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_asyncMode_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v_asyncMode_835_ = lean_ctor_get(v_toEnvExtension_820_, 2);
v___x_836_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_814_, v_env_821_, v_entry_813_, v_asyncMode_835_, v___x_816_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_836_);
v___x_838_ = v___x_833_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_messages_822_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_scopes_823_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_usedQuotCtxts_824_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_nextMacroScope_825_);
lean_ctor_set(v_reuseFailAlloc_842_, 5, v_maxRecDepth_826_);
lean_ctor_set(v_reuseFailAlloc_842_, 6, v_ngen_827_);
lean_ctor_set(v_reuseFailAlloc_842_, 7, v_auxDeclNGen_828_);
lean_ctor_set(v_reuseFailAlloc_842_, 8, v_infoState_829_);
lean_ctor_set(v_reuseFailAlloc_842_, 9, v_traceState_830_);
lean_ctor_set(v_reuseFailAlloc_842_, 10, v_snapshotTasks_831_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_st_ref_set(v___y_818_, v___x_838_);
v___x_840_ = lean_box(0);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___boxed(lean_object* v_mod_889_, lean_object* v_isMeta_890_, lean_object* v_hint_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v_isMeta_boxed_895_; lean_object* v_res_896_; 
v_isMeta_boxed_895_ = lean_unbox(v_isMeta_890_);
v_res_896_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_mod_889_, v_isMeta_boxed_895_, v_hint_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(lean_object* v___x_897_, lean_object* v_declName_898_, lean_object* v_as_899_, size_t v_sz_900_, size_t v_i_901_, lean_object* v_b_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = lean_usize_dec_lt(v_i_901_, v_sz_900_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
lean_dec(v_declName_898_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v_b_902_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; lean_object* v_modules_909_; lean_object* v___x_910_; lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v_toImport_913_; lean_object* v_module_914_; uint8_t v___x_915_; lean_object* v___x_916_; 
v___x_908_ = l_Lean_Environment_header(v___x_897_);
v_modules_909_ = lean_ctor_get(v___x_908_, 3);
lean_inc_ref(v_modules_909_);
lean_dec_ref(v___x_908_);
v___x_910_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_911_ = lean_array_uget_borrowed(v_as_899_, v_i_901_);
v___x_912_ = lean_array_get(v___x_910_, v_modules_909_, v_a_911_);
lean_dec_ref(v_modules_909_);
v_toImport_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_toImport_913_);
lean_dec(v___x_912_);
v_module_914_ = lean_ctor_get(v_toImport_913_, 0);
lean_inc(v_module_914_);
lean_dec_ref(v_toImport_913_);
v___x_915_ = 0;
lean_inc(v_declName_898_);
v___x_916_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_914_, v___x_915_, v_declName_898_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v___x_917_; size_t v___x_918_; size_t v___x_919_; 
lean_dec_ref_known(v___x_916_, 1);
v___x_917_ = lean_box(0);
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_add(v_i_901_, v___x_918_);
v_i_901_ = v___x_919_;
v_b_902_ = v___x_917_;
goto _start;
}
else
{
lean_dec(v_declName_898_);
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___boxed(lean_object* v___x_921_, lean_object* v_declName_922_, lean_object* v_as_923_, lean_object* v_sz_924_, lean_object* v_i_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
size_t v_sz_boxed_930_; size_t v_i_boxed_931_; lean_object* v_res_932_; 
v_sz_boxed_930_ = lean_unbox_usize(v_sz_924_);
lean_dec(v_sz_924_);
v_i_boxed_931_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_res_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v___x_921_, v_declName_922_, v_as_923_, v_sz_boxed_930_, v_i_boxed_931_, v_b_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec_ref(v_as_923_);
lean_dec_ref(v___x_921_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_a_933_, lean_object* v_x_934_){
_start:
{
if (lean_obj_tag(v_x_934_) == 0)
{
lean_object* v___x_935_; 
v___x_935_ = lean_box(0);
return v___x_935_;
}
else
{
lean_object* v_key_936_; lean_object* v_value_937_; lean_object* v_tail_938_; uint8_t v___x_939_; 
v_key_936_ = lean_ctor_get(v_x_934_, 0);
v_value_937_ = lean_ctor_get(v_x_934_, 1);
v_tail_938_ = lean_ctor_get(v_x_934_, 2);
v___x_939_ = lean_name_eq(v_key_936_, v_a_933_);
if (v___x_939_ == 0)
{
v_x_934_ = v_tail_938_;
goto _start;
}
else
{
lean_object* v___x_941_; 
lean_inc(v_value_937_);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v_value_937_);
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_a_942_, lean_object* v_x_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_942_, v_x_943_);
lean_dec(v_x_943_);
lean_dec(v_a_942_);
return v_res_944_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_945_; uint64_t v___x_946_; 
v___x_945_ = lean_unsigned_to_nat(1723u);
v___x_946_ = lean_uint64_of_nat(v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(lean_object* v_m_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_buckets_949_; lean_object* v___x_950_; uint64_t v___y_952_; 
v_buckets_949_ = lean_ctor_get(v_m_947_, 1);
v___x_950_ = lean_array_get_size(v_buckets_949_);
if (lean_obj_tag(v_a_948_) == 0)
{
uint64_t v___x_966_; 
v___x_966_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0);
v___y_952_ = v___x_966_;
goto v___jp_951_;
}
else
{
uint64_t v_hash_967_; 
v_hash_967_ = lean_ctor_get_uint64(v_a_948_, sizeof(void*)*2);
v___y_952_ = v_hash_967_;
goto v___jp_951_;
}
v___jp_951_:
{
uint64_t v___x_953_; uint64_t v___x_954_; uint64_t v_fold_955_; uint64_t v___x_956_; uint64_t v___x_957_; uint64_t v___x_958_; size_t v___x_959_; size_t v___x_960_; size_t v___x_961_; size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_953_ = 32ULL;
v___x_954_ = lean_uint64_shift_right(v___y_952_, v___x_953_);
v_fold_955_ = lean_uint64_xor(v___y_952_, v___x_954_);
v___x_956_ = 16ULL;
v___x_957_ = lean_uint64_shift_right(v_fold_955_, v___x_956_);
v___x_958_ = lean_uint64_xor(v_fold_955_, v___x_957_);
v___x_959_ = lean_uint64_to_usize(v___x_958_);
v___x_960_ = lean_usize_of_nat(v___x_950_);
v___x_961_ = ((size_t)1ULL);
v___x_962_ = lean_usize_sub(v___x_960_, v___x_961_);
v___x_963_ = lean_usize_land(v___x_959_, v___x_962_);
v___x_964_ = lean_array_uget_borrowed(v_buckets_949_, v___x_963_);
v___x_965_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_948_, v___x_964_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_m_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_968_, v_a_969_);
lean_dec(v_a_969_);
lean_dec_ref(v_m_968_);
return v_res_970_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1));
v___x_974_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0));
v___x_975_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_974_, v___x_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(lean_object* v_declName_978_, uint8_t v_isMeta_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; lean_object* v_env_987_; lean_object* v___y_989_; lean_object* v___x_1002_; 
v___x_983_ = lean_st_ref_get(v___y_981_);
v_env_987_ = lean_ctor_get(v___x_983_, 0);
lean_inc_ref(v_env_987_);
lean_dec(v___x_983_);
v___x_1002_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_987_, v_declName_978_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_dec_ref(v_env_987_);
lean_dec(v_declName_978_);
goto v___jp_984_;
}
else
{
lean_object* v_val_1003_; lean_object* v___x_1004_; lean_object* v_modules_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_val_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_val_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = l_Lean_Environment_header(v_env_987_);
v_modules_1005_ = lean_ctor_get(v___x_1004_, 3);
lean_inc_ref(v_modules_1005_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = lean_array_get_size(v_modules_1005_);
v___x_1007_ = lean_nat_dec_lt(v_val_1003_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_dec_ref(v_modules_1005_);
lean_dec(v_val_1003_);
lean_dec_ref(v_env_987_);
lean_dec(v_declName_978_);
goto v___jp_984_;
}
else
{
lean_object* v___x_1008_; lean_object* v_env_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___y_1013_; 
v___x_1008_ = lean_st_ref_get(v___y_981_);
v_env_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_ref(v_env_1009_);
lean_dec(v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2);
v___x_1011_ = lean_array_fget(v_modules_1005_, v_val_1003_);
lean_dec(v_val_1003_);
lean_dec_ref(v_modules_1005_);
if (v_isMeta_979_ == 0)
{
lean_dec_ref(v_env_1009_);
v___y_1013_ = v_isMeta_979_;
goto v___jp_1012_;
}
else
{
uint8_t v___x_1024_; 
lean_inc(v_declName_978_);
v___x_1024_ = l_Lean_isMarkedMeta(v_env_1009_, v_declName_978_);
if (v___x_1024_ == 0)
{
v___y_1013_ = v_isMeta_979_;
goto v___jp_1012_;
}
else
{
uint8_t v___x_1025_; 
v___x_1025_ = 0;
v___y_1013_ = v___x_1025_;
goto v___jp_1012_;
}
}
v___jp_1012_:
{
lean_object* v_toImport_1014_; lean_object* v_module_1015_; lean_object* v___x_1016_; 
v_toImport_1014_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_ref(v_toImport_1014_);
lean_dec(v___x_1011_);
v_module_1015_ = lean_ctor_get(v_toImport_1014_, 0);
lean_inc(v_module_1015_);
lean_dec_ref(v_toImport_1014_);
lean_inc(v_declName_978_);
v___x_1016_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_1015_, v___y_1013_, v_declName_978_, v___y_980_, v___y_981_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec_ref_known(v___x_1016_, 1);
v___x_1017_ = l_Lean_indirectModUseExt;
v___x_1018_ = lean_box(1);
v___x_1019_ = lean_box(0);
lean_inc_ref(v_env_987_);
v___x_1020_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1010_, v___x_1017_, v_env_987_, v___x_1018_, v___x_1019_);
v___x_1021_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v___x_1020_, v_declName_978_);
lean_dec(v___x_1020_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3));
v___y_989_ = v___x_1022_;
goto v___jp_988_;
}
else
{
lean_object* v_val_1023_; 
v_val_1023_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v___x_1021_, 1);
v___y_989_ = v_val_1023_;
goto v___jp_988_;
}
}
else
{
lean_dec_ref(v_env_987_);
lean_dec(v_declName_978_);
return v___x_1016_;
}
}
}
}
v___jp_984_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_box(0);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
v___jp_988_:
{
lean_object* v___x_990_; size_t v_sz_991_; size_t v___x_992_; lean_object* v___x_993_; 
v___x_990_ = lean_box(0);
v_sz_991_ = lean_array_size(v___y_989_);
v___x_992_ = ((size_t)0ULL);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v_env_987_, v_declName_978_, v___y_989_, v_sz_991_, v___x_992_, v___x_990_, v___y_980_, v___y_981_);
lean_dec_ref(v___y_989_);
lean_dec_ref(v_env_987_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v___x_993_, 0);
lean_dec(v_unused_1001_);
v___x_995_ = v___x_993_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_dec(v___x_993_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_990_);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_990_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
else
{
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___boxed(lean_object* v_declName_1026_, lean_object* v_isMeta_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v_isMeta_boxed_1031_; lean_object* v_res_1032_; 
v_isMeta_boxed_1031_ = lean_unbox(v_isMeta_1027_);
v_res_1032_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_declName_1026_, v_isMeta_boxed_1031_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(lean_object* v_as_x27_1033_, lean_object* v_b_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
if (lean_obj_tag(v_as_x27_1033_) == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_b_1034_);
return v___x_1038_;
}
else
{
lean_object* v_head_1039_; lean_object* v_tail_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; 
v_head_1039_ = lean_ctor_get(v_as_x27_1033_, 0);
v_tail_1040_ = lean_ctor_get(v_as_x27_1033_, 1);
v___x_1041_ = 1;
lean_inc(v_head_1039_);
v___x_1042_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_head_1039_, v___x_1041_, v___y_1035_, v___y_1036_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v___x_1043_; 
lean_dec_ref_known(v___x_1042_, 1);
v___x_1043_ = lean_box(0);
v_as_x27_1033_ = v_tail_1040_;
v_b_1034_ = v___x_1043_;
goto _start;
}
else
{
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg___boxed(lean_object* v_as_x27_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_1045_, v_b_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v_as_x27_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(lean_object* v_opts_1051_, lean_object* v_opt_1052_){
_start:
{
lean_object* v_name_1053_; lean_object* v_defValue_1054_; lean_object* v_map_1055_; lean_object* v___x_1056_; 
v_name_1053_ = lean_ctor_get(v_opt_1052_, 0);
v_defValue_1054_ = lean_ctor_get(v_opt_1052_, 1);
v_map_1055_ = lean_ctor_get(v_opts_1051_, 0);
v___x_1056_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1055_, v_name_1053_);
if (lean_obj_tag(v___x_1056_) == 0)
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_unbox(v_defValue_1054_);
return v___x_1057_;
}
else
{
lean_object* v_val_1058_; 
v_val_1058_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v___x_1056_, 1);
if (lean_obj_tag(v_val_1058_) == 1)
{
uint8_t v_v_1059_; 
v_v_1059_ = lean_ctor_get_uint8(v_val_1058_, 0);
lean_dec_ref_known(v_val_1058_, 0);
return v_v_1059_;
}
else
{
uint8_t v___x_1060_; 
lean_dec(v_val_1058_);
v___x_1060_ = lean_unbox(v_defValue_1054_);
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18___boxed(lean_object* v_opts_1061_, lean_object* v_opt_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(v_opts_1061_, v_opt_1062_);
lean_dec_ref(v_opt_1062_);
lean_dec_ref(v_opts_1061_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_box(1);
v___x_1066_ = l_Lean_MessageData_ofFormat(v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2));
v___x_1071_ = l_Lean_MessageData_ofFormat(v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(lean_object* v_x_1072_, lean_object* v_x_1073_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 0)
{
return v_x_1072_;
}
else
{
lean_object* v_head_1074_; lean_object* v_tail_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1097_; 
v_head_1074_ = lean_ctor_get(v_x_1073_, 0);
v_tail_1075_ = lean_ctor_get(v_x_1073_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1077_ = v_x_1073_;
v_isShared_1078_ = v_isSharedCheck_1097_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_tail_1075_);
lean_inc(v_head_1074_);
lean_dec(v_x_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1097_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_before_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1095_; 
v_before_1079_ = lean_ctor_get(v_head_1074_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_head_1074_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v_head_1074_, 1);
lean_dec(v_unused_1096_);
v___x_1081_ = v_head_1074_;
v_isShared_1082_ = v_isSharedCheck_1095_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_before_1079_);
lean_dec(v_head_1074_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1095_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0);
if (v_isShared_1082_ == 0)
{
lean_ctor_set_tag(v___x_1081_, 7);
lean_ctor_set(v___x_1081_, 1, v___x_1083_);
lean_ctor_set(v___x_1081_, 0, v_x_1072_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_x_1072_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3);
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 7);
lean_ctor_set(v___x_1077_, 1, v___x_1086_);
lean_ctor_set(v___x_1077_, 0, v___x_1085_);
v___x_1088_ = v___x_1077_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = l_Lean_MessageData_ofSyntax(v_before_1079_);
v___x_1090_ = l_Lean_indentD(v___x_1089_);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1088_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v_x_1072_ = v___x_1091_;
v_x_1073_ = v_tail_1075_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1));
v___x_1102_ = l_Lean_MessageData_ofFormat(v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(lean_object* v_msgData_1103_, lean_object* v_macroStack_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v_scopes_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_opts_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1107_ = lean_st_ref_get(v___y_1105_);
v_scopes_1108_ = lean_ctor_get(v___x_1107_, 2);
lean_inc(v_scopes_1108_);
lean_dec(v___x_1107_);
v___x_1109_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1110_ = l_List_head_x21___redArg(v___x_1109_, v_scopes_1108_);
lean_dec(v_scopes_1108_);
v_opts_1111_ = lean_ctor_get(v___x_1110_, 1);
lean_inc_ref(v_opts_1111_);
lean_dec(v___x_1110_);
v___x_1112_ = l_Lean_Elab_pp_macroStack;
v___x_1113_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(v_opts_1111_, v___x_1112_);
lean_dec_ref(v_opts_1111_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_dec(v_macroStack_1104_);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_msgData_1103_);
return v___x_1114_;
}
else
{
if (lean_obj_tag(v_macroStack_1104_) == 0)
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v_msgData_1103_);
return v___x_1115_;
}
else
{
lean_object* v_head_1116_; lean_object* v_after_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1132_; 
v_head_1116_ = lean_ctor_get(v_macroStack_1104_, 0);
lean_inc(v_head_1116_);
v_after_1117_ = lean_ctor_get(v_head_1116_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_head_1116_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; 
v_unused_1133_ = lean_ctor_get(v_head_1116_, 0);
lean_dec(v_unused_1133_);
v___x_1119_ = v_head_1116_;
v_isShared_1120_ = v_isSharedCheck_1132_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_after_1117_);
lean_dec(v_head_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1132_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1121_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0);
if (v_isShared_1120_ == 0)
{
lean_ctor_set_tag(v___x_1119_, 7);
lean_ctor_set(v___x_1119_, 1, v___x_1121_);
lean_ctor_set(v___x_1119_, 0, v_msgData_1103_);
v___x_1123_ = v___x_1119_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_msgData_1103_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_msgData_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1124_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_MessageData_ofSyntax(v_after_1117_);
v___x_1127_ = l_Lean_indentD(v___x_1126_);
v_msgData_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1128_, 0, v___x_1125_);
lean_ctor_set(v_msgData_1128_, 1, v___x_1127_);
v___x_1129_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(v_msgData_1128_, v_macroStack_1104_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___boxed(lean_object* v_msgData_1134_, lean_object* v_macroStack_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_1134_, v_macroStack_1135_, v___y_1136_);
lean_dec(v___y_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(lean_object* v_msg_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Elab_Command_getRef___redArg(v___y_1140_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v_macroStack_1145_; lean_object* v___x_1146_; lean_object* v_a_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1158_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v_macroStack_1145_ = lean_ctor_get(v___y_1140_, 4);
v___x_1146_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_1139_, v___y_1141_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref(v___x_1146_);
v___x_1148_ = l_Lean_Elab_getBetterRef(v_a_1144_, v_macroStack_1145_);
lean_dec(v_a_1144_);
lean_inc(v_macroStack_1145_);
v___x_1149_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_a_1147_, v_macroStack_1145_, v___y_1141_);
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1148_);
lean_ctor_set(v___x_1154_, 1, v_a_1150_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 1);
lean_ctor_set(v___x_1152_, 0, v___x_1154_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v_msg_1139_);
v_a_1159_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1143_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1143_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg___boxed(lean_object* v_msg_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(lean_object* v_ref_1172_, lean_object* v_msg_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Lean_Elab_Command_getRef___redArg(v___y_1174_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v_fileName_1179_; lean_object* v_fileMap_1180_; lean_object* v_currRecDepth_1181_; lean_object* v_cmdPos_1182_; lean_object* v_macroStack_1183_; lean_object* v_quotContext_x3f_1184_; lean_object* v_currMacroScope_1185_; lean_object* v_snap_x3f_1186_; lean_object* v_cancelTk_x3f_1187_; uint8_t v_suppressElabErrors_1188_; lean_object* v_ref_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v_fileName_1179_ = lean_ctor_get(v___y_1174_, 0);
v_fileMap_1180_ = lean_ctor_get(v___y_1174_, 1);
v_currRecDepth_1181_ = lean_ctor_get(v___y_1174_, 2);
v_cmdPos_1182_ = lean_ctor_get(v___y_1174_, 3);
v_macroStack_1183_ = lean_ctor_get(v___y_1174_, 4);
v_quotContext_x3f_1184_ = lean_ctor_get(v___y_1174_, 5);
v_currMacroScope_1185_ = lean_ctor_get(v___y_1174_, 6);
v_snap_x3f_1186_ = lean_ctor_get(v___y_1174_, 8);
v_cancelTk_x3f_1187_ = lean_ctor_get(v___y_1174_, 9);
v_suppressElabErrors_1188_ = lean_ctor_get_uint8(v___y_1174_, sizeof(void*)*10);
v_ref_1189_ = l_Lean_replaceRef(v_ref_1172_, v_a_1178_);
lean_dec(v_a_1178_);
lean_inc(v_cancelTk_x3f_1187_);
lean_inc(v_snap_x3f_1186_);
lean_inc(v_currMacroScope_1185_);
lean_inc(v_quotContext_x3f_1184_);
lean_inc(v_macroStack_1183_);
lean_inc(v_cmdPos_1182_);
lean_inc(v_currRecDepth_1181_);
lean_inc_ref(v_fileMap_1180_);
lean_inc_ref(v_fileName_1179_);
v___x_1190_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1190_, 0, v_fileName_1179_);
lean_ctor_set(v___x_1190_, 1, v_fileMap_1180_);
lean_ctor_set(v___x_1190_, 2, v_currRecDepth_1181_);
lean_ctor_set(v___x_1190_, 3, v_cmdPos_1182_);
lean_ctor_set(v___x_1190_, 4, v_macroStack_1183_);
lean_ctor_set(v___x_1190_, 5, v_quotContext_x3f_1184_);
lean_ctor_set(v___x_1190_, 6, v_currMacroScope_1185_);
lean_ctor_set(v___x_1190_, 7, v_ref_1189_);
lean_ctor_set(v___x_1190_, 8, v_snap_x3f_1186_);
lean_ctor_set(v___x_1190_, 9, v_cancelTk_x3f_1187_);
lean_ctor_set_uint8(v___x_1190_, sizeof(void*)*10, v_suppressElabErrors_1188_);
v___x_1191_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1173_, v___x_1190_, v___y_1175_);
lean_dec_ref_known(v___x_1190_, 10);
return v___x_1191_;
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v_msg_1173_);
v_a_1192_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1177_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1177_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1200_, lean_object* v_msg_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_1200_, v_msg_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v_ref_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(lean_object* v_env_1206_, lean_object* v_declName_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
uint8_t v___x_1210_; lean_object* v_env_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1210_ = 0;
v_env_1211_ = l_Lean_Environment_setExporting(v_env_1206_, v___x_1210_);
lean_inc(v_declName_1207_);
v___x_1212_ = l_Lean_mkPrivateName(v_env_1211_, v_declName_1207_);
v___x_1213_ = 1;
lean_inc_ref(v_env_1211_);
v___x_1214_ = l_Lean_Environment_contains(v_env_1211_, v___x_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1215_ = l_Lean_privateToUserName(v_declName_1207_);
v___x_1216_ = l_Lean_Environment_contains(v_env_1211_, v___x_1215_, v___x_1213_);
v___x_1217_ = lean_box(v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v___y_1209_);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec_ref(v_env_1211_);
lean_dec(v_declName_1207_);
v___x_1219_ = lean_box(v___x_1214_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v___y_1209_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed(lean_object* v_env_1221_, lean_object* v_declName_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(v_env_1221_, v_declName_1222_, v___y_1223_, v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(lean_object* v_as_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
if (lean_obj_tag(v_as_1226_) == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
else
{
lean_object* v_head_1232_; lean_object* v_tail_1233_; lean_object* v_fst_1234_; lean_object* v_snd_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_scopes_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v_opts_1242_; uint8_t v_hasTrace_1243_; 
v_head_1232_ = lean_ctor_get(v_as_1226_, 0);
lean_inc(v_head_1232_);
v_tail_1233_ = lean_ctor_get(v_as_1226_, 1);
lean_inc(v_tail_1233_);
lean_dec_ref_known(v_as_1226_, 2);
v_fst_1234_ = lean_ctor_get(v_head_1232_, 0);
lean_inc(v_fst_1234_);
v_snd_1235_ = lean_ctor_get(v_head_1232_, 1);
lean_inc(v_snd_1235_);
lean_dec(v_head_1232_);
v___x_1236_ = l_Lean_inheritedTraceOptions;
v___x_1237_ = lean_st_ref_get(v___x_1236_);
v___x_1238_ = lean_st_ref_get(v___y_1228_);
v_scopes_1239_ = lean_ctor_get(v___x_1238_, 2);
lean_inc(v_scopes_1239_);
lean_dec(v___x_1238_);
v___x_1240_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1241_ = l_List_head_x21___redArg(v___x_1240_, v_scopes_1239_);
lean_dec(v_scopes_1239_);
v_opts_1242_ = lean_ctor_get(v___x_1241_, 1);
lean_inc_ref(v_opts_1242_);
lean_dec(v___x_1241_);
v_hasTrace_1243_ = lean_ctor_get_uint8(v_opts_1242_, sizeof(void*)*1);
if (v_hasTrace_1243_ == 0)
{
lean_dec_ref(v_opts_1242_);
lean_dec(v___x_1237_);
lean_dec(v_snd_1235_);
lean_dec(v_fst_1234_);
v_as_1226_ = v_tail_1233_;
goto _start;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1245_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11));
lean_inc(v_fst_1234_);
v___x_1246_ = l_Lean_Name_append(v___x_1245_, v_fst_1234_);
v___x_1247_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1237_, v_opts_1242_, v___x_1246_);
lean_dec(v___x_1246_);
lean_dec_ref(v_opts_1242_);
lean_dec(v___x_1237_);
if (v___x_1247_ == 0)
{
lean_dec(v_snd_1235_);
lean_dec(v_fst_1234_);
v_as_1226_ = v_tail_1233_;
goto _start;
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_snd_1235_);
v___x_1250_ = l_Lean_MessageData_ofFormat(v___x_1249_);
v___x_1251_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_fst_1234_, v___x_1250_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_dec_ref_known(v___x_1251_, 1);
v_as_1226_ = v_tail_1233_;
goto _start;
}
else
{
lean_dec(v_tail_1233_);
return v___x_1251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3___boxed(lean_object* v_as_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v_as_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(lean_object* v_env_1258_, lean_object* v_opts_1259_, lean_object* v_currNamespace_1260_, lean_object* v_openDecls_1261_, lean_object* v_n_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = l_Lean_ResolveName_resolveGlobalName(v_env_1258_, v_opts_1259_, v_currNamespace_1260_, v_openDecls_1261_, v_n_1262_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v___y_1264_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed(lean_object* v_env_1267_, lean_object* v_opts_1268_, lean_object* v_currNamespace_1269_, lean_object* v_openDecls_1270_, lean_object* v_n_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(v_env_1267_, v_opts_1268_, v_currNamespace_1269_, v_openDecls_1270_, v_n_1271_, v___y_1272_, v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v_opts_1268_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(lean_object* v_x_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v_env_1281_; lean_object* v___x_1282_; lean_object* v_scopes_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_opts_1286_; lean_object* v___x_1287_; 
v___x_1280_ = lean_st_ref_get(v___y_1278_);
v_env_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc_ref(v_env_1281_);
lean_dec(v___x_1280_);
v___x_1282_ = lean_st_ref_get(v___y_1278_);
v_scopes_1283_ = lean_ctor_get(v___x_1282_, 2);
lean_inc(v_scopes_1283_);
lean_dec(v___x_1282_);
v___x_1284_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1285_ = l_List_head_x21___redArg(v___x_1284_, v_scopes_1283_);
lean_dec(v_scopes_1283_);
v_opts_1286_ = lean_ctor_get(v___x_1285_, 1);
lean_inc_ref(v_opts_1286_);
lean_dec(v___x_1285_);
v___x_1287_ = l_Lean_Elab_Command_getScope___redArg(v___y_1278_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v_currNamespace_1289_; lean_object* v___x_1290_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v_currNamespace_1289_ = lean_ctor_get(v_a_1288_, 2);
lean_inc(v_currNamespace_1289_);
lean_dec(v_a_1288_);
v___x_1290_ = l_Lean_Elab_Command_getScope___redArg(v___y_1278_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v_openDecls_1292_; lean_object* v___x_1293_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v_openDecls_1292_ = lean_ctor_get(v_a_1291_, 3);
lean_inc(v_openDecls_1292_);
lean_dec(v_a_1291_);
v___x_1293_ = l_Lean_Elab_Command_getRef___redArg(v___y_1277_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1295_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1277_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v_currRecDepth_1297_; lean_object* v_quotContext_x3f_1298_; lean_object* v___f_1299_; lean_object* v___f_1300_; lean_object* v___f_1301_; lean_object* v___f_1302_; lean_object* v___f_1303_; lean_object* v_methods_1304_; lean_object* v_a_1306_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
v_currRecDepth_1297_ = lean_ctor_get(v___y_1277_, 2);
v_quotContext_x3f_1298_ = lean_ctor_get(v___y_1277_, 5);
lean_inc_ref_n(v_env_1281_, 3);
v___f_1299_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1299_, 0, v_env_1281_);
v___f_1300_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1300_, 0, v_env_1281_);
lean_inc_n(v_currNamespace_1289_, 2);
v___f_1301_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1301_, 0, v_currNamespace_1289_);
lean_inc(v_openDecls_1292_);
v___f_1302_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1302_, 0, v_env_1281_);
lean_closure_set(v___f_1302_, 1, v_currNamespace_1289_);
lean_closure_set(v___f_1302_, 2, v_openDecls_1292_);
v___f_1303_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1303_, 0, v_env_1281_);
lean_closure_set(v___f_1303_, 1, v_opts_1286_);
lean_closure_set(v___f_1303_, 2, v_currNamespace_1289_);
lean_closure_set(v___f_1303_, 3, v_openDecls_1292_);
v_methods_1304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1304_, 0, v___f_1300_);
lean_ctor_set(v_methods_1304_, 1, v___f_1301_);
lean_ctor_set(v_methods_1304_, 2, v___f_1299_);
lean_ctor_set(v_methods_1304_, 3, v___f_1302_);
lean_ctor_set(v_methods_1304_, 4, v___f_1303_);
if (lean_obj_tag(v_quotContext_x3f_1298_) == 0)
{
lean_object* v___x_1378_; lean_object* v_a_1379_; 
v___x_1378_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_1278_);
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref(v___x_1378_);
v_a_1306_ = v_a_1379_;
goto v___jp_1305_;
}
else
{
lean_object* v_val_1380_; 
v_val_1380_ = lean_ctor_get(v_quotContext_x3f_1298_, 0);
lean_inc(v_val_1380_);
v_a_1306_ = v_val_1380_;
goto v___jp_1305_;
}
v___jp_1305_:
{
lean_object* v___x_1307_; lean_object* v_maxRecDepth_1308_; lean_object* v___x_1309_; lean_object* v_nextMacroScope_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1307_ = lean_st_ref_get(v___y_1278_);
v_maxRecDepth_1308_ = lean_ctor_get(v___x_1307_, 5);
lean_inc(v_maxRecDepth_1308_);
lean_dec(v___x_1307_);
v___x_1309_ = lean_st_ref_get(v___y_1278_);
v_nextMacroScope_1310_ = lean_ctor_get(v___x_1309_, 4);
lean_inc(v_nextMacroScope_1310_);
lean_dec(v___x_1309_);
lean_inc(v_currRecDepth_1297_);
v___x_1311_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1311_, 0, v_methods_1304_);
lean_ctor_set(v___x_1311_, 1, v_a_1306_);
lean_ctor_set(v___x_1311_, 2, v_a_1296_);
lean_ctor_set(v___x_1311_, 3, v_currRecDepth_1297_);
lean_ctor_set(v___x_1311_, 4, v_maxRecDepth_1308_);
lean_ctor_set(v___x_1311_, 5, v_a_1294_);
v___x_1312_ = lean_box(0);
v___x_1313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1313_, 0, v_nextMacroScope_1310_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
lean_ctor_set(v___x_1313_, 2, v___x_1312_);
v___x_1314_ = lean_apply_2(v_x_1276_, v___x_1311_, v___x_1313_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v_a_1316_; lean_object* v_macroScope_1317_; lean_object* v_traceMsgs_1318_; lean_object* v_expandedMacroDecls_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 1);
lean_inc(v_a_1315_);
v_a_1316_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1314_, 2);
v_macroScope_1317_ = lean_ctor_get(v_a_1315_, 0);
lean_inc(v_macroScope_1317_);
v_traceMsgs_1318_ = lean_ctor_get(v_a_1315_, 1);
lean_inc(v_traceMsgs_1318_);
v_expandedMacroDecls_1319_ = lean_ctor_get(v_a_1315_, 2);
lean_inc(v_expandedMacroDecls_1319_);
lean_dec(v_a_1315_);
v___x_1320_ = lean_box(0);
v___x_1321_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_expandedMacroDecls_1319_, v___x_1320_, v___y_1277_, v___y_1278_);
lean_dec(v_expandedMacroDecls_1319_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v___x_1322_; lean_object* v_env_1323_; lean_object* v_messages_1324_; lean_object* v_scopes_1325_; lean_object* v_usedQuotCtxts_1326_; lean_object* v_maxRecDepth_1327_; lean_object* v_ngen_1328_; lean_object* v_auxDeclNGen_1329_; lean_object* v_infoState_1330_; lean_object* v_traceState_1331_; lean_object* v_snapshotTasks_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref_known(v___x_1321_, 1);
v___x_1322_ = lean_st_ref_take(v___y_1278_);
v_env_1323_ = lean_ctor_get(v___x_1322_, 0);
v_messages_1324_ = lean_ctor_get(v___x_1322_, 1);
v_scopes_1325_ = lean_ctor_get(v___x_1322_, 2);
v_usedQuotCtxts_1326_ = lean_ctor_get(v___x_1322_, 3);
v_maxRecDepth_1327_ = lean_ctor_get(v___x_1322_, 5);
v_ngen_1328_ = lean_ctor_get(v___x_1322_, 6);
v_auxDeclNGen_1329_ = lean_ctor_get(v___x_1322_, 7);
v_infoState_1330_ = lean_ctor_get(v___x_1322_, 8);
v_traceState_1331_ = lean_ctor_get(v___x_1322_, 9);
v_snapshotTasks_1332_ = lean_ctor_get(v___x_1322_, 10);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v___x_1322_, 4);
lean_dec(v_unused_1359_);
v___x_1334_ = v___x_1322_;
v_isShared_1335_ = v_isSharedCheck_1358_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_snapshotTasks_1332_);
lean_inc(v_traceState_1331_);
lean_inc(v_infoState_1330_);
lean_inc(v_auxDeclNGen_1329_);
lean_inc(v_ngen_1328_);
lean_inc(v_maxRecDepth_1327_);
lean_inc(v_usedQuotCtxts_1326_);
lean_inc(v_scopes_1325_);
lean_inc(v_messages_1324_);
lean_inc(v_env_1323_);
lean_dec(v___x_1322_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1358_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 4, v_macroScope_1317_);
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_env_1323_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_messages_1324_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_scopes_1325_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_usedQuotCtxts_1326_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_macroScope_1317_);
lean_ctor_set(v_reuseFailAlloc_1357_, 5, v_maxRecDepth_1327_);
lean_ctor_set(v_reuseFailAlloc_1357_, 6, v_ngen_1328_);
lean_ctor_set(v_reuseFailAlloc_1357_, 7, v_auxDeclNGen_1329_);
lean_ctor_set(v_reuseFailAlloc_1357_, 8, v_infoState_1330_);
lean_ctor_set(v_reuseFailAlloc_1357_, 9, v_traceState_1331_);
lean_ctor_set(v_reuseFailAlloc_1357_, 10, v_snapshotTasks_1332_);
v___x_1337_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = lean_st_ref_set(v___y_1278_, v___x_1337_);
v___x_1339_ = l_List_reverse___redArg(v_traceMsgs_1318_);
v___x_1340_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v___x_1339_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___x_1340_, 0);
lean_dec(v_unused_1348_);
v___x_1342_ = v___x_1340_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_dec(v___x_1340_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v_a_1316_);
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1316_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_a_1316_);
v_a_1349_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1340_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1340_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_traceMsgs_1318_);
lean_dec(v_macroScope_1317_);
lean_dec(v_a_1316_);
v_a_1360_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1321_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1321_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v_a_1368_; 
v_a_1368_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1314_, 2);
if (lean_obj_tag(v_a_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v_a_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_a_1369_ = lean_ctor_get(v_a_1368_, 0);
lean_inc(v_a_1369_);
v_a_1370_ = lean_ctor_get(v_a_1368_, 1);
lean_inc_ref(v_a_1370_);
lean_dec_ref_known(v_a_1368_, 2);
v___x_1371_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0));
v___x_1372_ = lean_string_dec_eq(v_a_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_a_1370_);
v___x_1374_ = l_Lean_MessageData_ofFormat(v___x_1373_);
v___x_1375_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_a_1369_, v___x_1374_, v___y_1277_, v___y_1278_);
lean_dec(v_a_1369_);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; 
lean_dec_ref(v_a_1370_);
v___x_1376_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_a_1369_);
return v___x_1376_;
}
}
else
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_a_1294_);
lean_dec(v_openDecls_1292_);
lean_dec(v_currNamespace_1289_);
lean_dec_ref(v_opts_1286_);
lean_dec_ref(v_env_1281_);
lean_dec_ref(v_x_1276_);
v_a_1381_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1295_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1295_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec(v_openDecls_1292_);
lean_dec(v_currNamespace_1289_);
lean_dec_ref(v_opts_1286_);
lean_dec_ref(v_env_1281_);
lean_dec_ref(v_x_1276_);
v_a_1389_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1293_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1293_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v_currNamespace_1289_);
lean_dec_ref(v_opts_1286_);
lean_dec_ref(v_env_1281_);
lean_dec_ref(v_x_1276_);
v_a_1397_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1290_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1290_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v_opts_1286_);
lean_dec_ref(v_env_1281_);
lean_dec_ref(v_x_1276_);
v_a_1405_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1287_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1287_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___boxed(lean_object* v_x_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v_x_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1417_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1433_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11));
v___x_1434_ = l_Lean_Name_append(v___x_1433_, v___x_1432_);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__8));
v___x_1437_ = l_Lean_stringToMessageData(v___x_1436_);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__10));
v___x_1440_ = l_Lean_stringToMessageData(v___x_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object* v_modifiers_1441_, lean_object* v_stx_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v___x_1446_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v_declId_1453_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1466_ = l_Lean_Syntax_getArg(v_stx_1442_, v___x_1446_);
v___x_1467_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_1467_, 0, v___x_1466_);
v___x_1468_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_1467_, v_a_1443_, v_a_1444_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
v___x_1470_ = lean_unsigned_to_nat(2u);
v___x_1493_ = l_Lean_Syntax_getArg(v_stx_1442_, v___x_1470_);
v___x_1494_ = lean_alloc_closure((void*)(l_Lean_Elab_expandOptNamedPrio___boxed), 3, 1);
lean_closure_set(v___x_1494_, 0, v___x_1493_);
v___x_1495_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_1494_, v_a_1443_, v_a_1444_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1497_ = l_Lean_Elab_Command_getRef___redArg(v_a_1443_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1499_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1443_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_quotContext_x3f_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; 
lean_dec_ref_known(v___x_1499_, 1);
v_quotContext_x3f_1500_ = lean_ctor_get(v_a_1443_, 5);
v___x_1501_ = 0;
v___x_1502_ = l_Lean_SourceInfo_fromRef(v_a_1498_, v___x_1501_);
lean_dec(v_a_1498_);
if (lean_obj_tag(v_quotContext_x3f_1500_) == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1444_);
lean_dec_ref(v___x_1637_);
goto v___jp_1503_;
}
else
{
goto v___jp_1503_;
}
v___jp_1503_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_fst_1507_; lean_object* v_snd_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1636_; 
v___x_1504_ = lean_unsigned_to_nat(4u);
v___x_1505_ = l_Lean_Syntax_getArg(v_stx_1442_, v___x_1504_);
v___x_1506_ = l_Lean_Elab_expandDeclSig(v___x_1505_);
lean_dec(v___x_1505_);
v_fst_1507_ = lean_ctor_get(v___x_1506_, 0);
v_snd_1508_ = lean_ctor_get(v___x_1506_, 1);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1510_ = v___x_1506_;
v_isShared_1511_ = v_isSharedCheck_1636_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_snd_1508_);
lean_inc(v_fst_1507_);
lean_dec(v___x_1506_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1636_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1512_ = ((lean_object*)(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_));
v___x_1513_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2));
v___x_1514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0));
v___x_1515_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4));
lean_inc(v___x_1502_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 2);
lean_ctor_set(v___x_1510_, 1, v___x_1514_);
lean_ctor_set(v___x_1510_, 0, v___x_1502_);
v___x_1517_ = v___x_1510_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v___x_1514_);
v___x_1517_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1518_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1519_ = l_Nat_reprFast(v_a_1496_);
v___x_1520_ = lean_box(2);
v___x_1521_ = l_Lean_Syntax_mkNumLit(v___x_1519_, v___x_1520_);
lean_inc(v___x_1502_);
v___x_1522_ = l_Lean_Syntax_node1(v___x_1502_, v___x_1518_, v___x_1521_);
v___x_1523_ = l_Lean_Syntax_node2(v___x_1502_, v___x_1515_, v___x_1517_, v___x_1522_);
v___x_1524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1));
v___x_1525_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v___x_1523_);
v___x_1526_ = lean_unbox(v_a_1469_);
lean_dec(v_a_1469_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*2, v___x_1526_);
v___x_1527_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_1441_, v___x_1525_);
v___x_1528_ = lean_unsigned_to_nat(3u);
v___x_1529_ = l_Lean_Syntax_getArg(v_stx_1442_, v___x_1528_);
v___x_1530_ = l_Lean_Syntax_getOptional_x3f(v___x_1529_);
lean_dec(v___x_1529_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = l_Lean_Syntax_getArgs(v_fst_1507_);
lean_inc(v_snd_1508_);
v___x_1532_ = l_Lean_Elab_Command_mkInstanceName(v___x_1531_, v_snd_1508_, v_a_1443_, v_a_1444_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_scopes_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v_opts_1540_; uint8_t v_hasTrace_1541_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = l_Lean_inheritedTraceOptions;
v___x_1535_ = lean_st_ref_get(v___x_1534_);
v___x_1536_ = lean_st_ref_get(v_a_1444_);
v_scopes_1537_ = lean_ctor_get(v___x_1536_, 2);
lean_inc(v_scopes_1537_);
lean_dec(v___x_1536_);
v___x_1538_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1539_ = l_List_head_x21___redArg(v___x_1538_, v_scopes_1537_);
lean_dec(v_scopes_1537_);
v_opts_1540_ = lean_ctor_get(v___x_1539_, 1);
lean_inc_ref(v_opts_1540_);
lean_dec(v___x_1539_);
v_hasTrace_1541_ = lean_ctor_get_uint8(v_opts_1540_, sizeof(void*)*1);
if (v_hasTrace_1541_ == 0)
{
lean_dec_ref(v_opts_1540_);
lean_dec(v___x_1535_);
v___y_1472_ = v_snd_1508_;
v___y_1473_ = v___x_1513_;
v___y_1474_ = v_fst_1507_;
v___y_1475_ = v_a_1533_;
v___y_1476_ = v___x_1527_;
v___y_1477_ = v___x_1512_;
v___y_1478_ = v___x_1518_;
v___y_1479_ = v___x_1520_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1542_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1543_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__7, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7);
v___x_1544_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1535_, v_opts_1540_, v___x_1543_);
lean_dec_ref(v_opts_1540_);
lean_dec(v___x_1535_);
if (v___x_1544_ == 0)
{
v___y_1472_ = v_snd_1508_;
v___y_1473_ = v___x_1513_;
v___y_1474_ = v_fst_1507_;
v___y_1475_ = v_a_1533_;
v___y_1476_ = v___x_1527_;
v___y_1477_ = v___x_1512_;
v___y_1478_ = v___x_1518_;
v___y_1479_ = v___x_1520_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_Elab_Command_getScope___redArg(v_a_1444_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v_currNamespace_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v_currNamespace_1547_ = lean_ctor_get(v_a_1546_, 2);
lean_inc(v_currNamespace_1547_);
lean_dec(v_a_1546_);
v___x_1548_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__9, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
lean_inc(v_a_1533_);
v___x_1549_ = l_Lean_Name_append(v_currNamespace_1547_, v_a_1533_);
v___x_1550_ = l_Lean_MessageData_ofName(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1548_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_1542_, v___x_1551_, v_a_1443_, v_a_1444_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_dec_ref_known(v___x_1552_, 1);
v___y_1472_ = v_snd_1508_;
v___y_1473_ = v___x_1513_;
v___y_1474_ = v_fst_1507_;
v___y_1475_ = v_a_1533_;
v___y_1476_ = v___x_1527_;
v___y_1477_ = v___x_1512_;
v___y_1478_ = v___x_1518_;
v___y_1479_ = v___x_1520_;
goto v___jp_1471_;
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1533_);
lean_dec_ref(v___x_1527_);
lean_dec(v_snd_1508_);
lean_dec(v_fst_1507_);
lean_dec(v_stx_1442_);
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec(v_a_1533_);
lean_dec_ref(v___x_1527_);
lean_dec(v_snd_1508_);
lean_dec(v_fst_1507_);
lean_dec(v_stx_1442_);
v_a_1561_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1545_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1545_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v___x_1527_);
lean_dec(v_snd_1508_);
lean_dec(v_fst_1507_);
lean_dec(v_stx_1442_);
v_a_1569_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1532_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1532_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v_val_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_scopes_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v_opts_1584_; uint8_t v_hasTrace_1585_; 
v_val_1577_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1578_ = l_Lean_inheritedTraceOptions;
v___x_1579_ = lean_st_ref_get(v___x_1578_);
v___x_1580_ = lean_st_ref_get(v_a_1444_);
v_scopes_1581_ = lean_ctor_get(v___x_1580_, 2);
lean_inc(v_scopes_1581_);
lean_dec(v___x_1580_);
v___x_1582_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1583_ = l_List_head_x21___redArg(v___x_1582_, v_scopes_1581_);
lean_dec(v_scopes_1581_);
v_opts_1584_ = lean_ctor_get(v___x_1583_, 1);
lean_inc_ref(v_opts_1584_);
lean_dec(v___x_1583_);
v_hasTrace_1585_ = lean_ctor_get_uint8(v_opts_1584_, sizeof(void*)*1);
if (v_hasTrace_1585_ == 0)
{
lean_dec_ref(v_opts_1584_);
lean_dec(v___x_1579_);
v___y_1448_ = v_snd_1508_;
v___y_1449_ = v_fst_1507_;
v___y_1450_ = v___x_1527_;
v___y_1451_ = v___x_1518_;
v___y_1452_ = v___x_1520_;
v_declId_1453_ = v_val_1577_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1586_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1587_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__7, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7);
v___x_1588_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1579_, v_opts_1584_, v___x_1587_);
lean_dec_ref(v_opts_1584_);
lean_dec(v___x_1579_);
if (v___x_1588_ == 0)
{
v___y_1448_ = v_snd_1508_;
v___y_1449_ = v_fst_1507_;
v___y_1450_ = v___x_1527_;
v___y_1451_ = v___x_1518_;
v___y_1452_ = v___x_1520_;
v_declId_1453_ = v_val_1577_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = l_Lean_Syntax_getArgs(v_fst_1507_);
lean_inc(v_snd_1508_);
v___x_1590_ = l_Lean_Elab_Command_mkInstanceName(v___x_1589_, v_snd_1508_, v_a_1443_, v_a_1444_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v_scopes_1594_; lean_object* v___x_1595_; lean_object* v_opts_1596_; uint8_t v_hasTrace_1597_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = lean_st_ref_get(v___x_1578_);
v___x_1593_ = lean_st_ref_get(v_a_1444_);
v_scopes_1594_ = lean_ctor_get(v___x_1593_, 2);
lean_inc(v_scopes_1594_);
lean_dec(v___x_1593_);
v___x_1595_ = l_List_head_x21___redArg(v___x_1582_, v_scopes_1594_);
lean_dec(v_scopes_1594_);
v_opts_1596_ = lean_ctor_get(v___x_1595_, 1);
lean_inc_ref(v_opts_1596_);
lean_dec(v___x_1595_);
v_hasTrace_1597_ = lean_ctor_get_uint8(v_opts_1596_, sizeof(void*)*1);
if (v_hasTrace_1597_ == 0)
{
lean_dec_ref(v_opts_1596_);
lean_dec(v___x_1592_);
lean_dec(v_a_1591_);
v___y_1448_ = v_snd_1508_;
v___y_1449_ = v_fst_1507_;
v___y_1450_ = v___x_1527_;
v___y_1451_ = v___x_1518_;
v___y_1452_ = v___x_1520_;
v_declId_1453_ = v_val_1577_;
goto v___jp_1447_;
}
else
{
uint8_t v___x_1598_; 
v___x_1598_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1592_, v_opts_1596_, v___x_1587_);
lean_dec_ref(v_opts_1596_);
lean_dec(v___x_1592_);
if (v___x_1598_ == 0)
{
lean_dec(v_a_1591_);
v___y_1448_ = v_snd_1508_;
v___y_1449_ = v_fst_1507_;
v___y_1450_ = v___x_1527_;
v___y_1451_ = v___x_1518_;
v___y_1452_ = v___x_1520_;
v_declId_1453_ = v_val_1577_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Elab_Command_getScope___redArg(v_a_1444_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v_currNamespace_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1599_, 1);
v_currNamespace_1601_ = lean_ctor_get(v_a_1600_, 2);
lean_inc(v_currNamespace_1601_);
lean_dec(v_a_1600_);
v___x_1602_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__9, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
v___x_1603_ = l_Lean_Name_append(v_currNamespace_1601_, v_a_1591_);
v___x_1604_ = l_Lean_MessageData_ofName(v___x_1603_);
v___x_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1602_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__11, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__11_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
lean_inc(v_val_1577_);
v___x_1608_ = l_Lean_MessageData_ofSyntax(v_val_1577_);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_1586_, v___x_1609_, v_a_1443_, v_a_1444_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_dec_ref_known(v___x_1610_, 1);
v___y_1448_ = v_snd_1508_;
v___y_1449_ = v_fst_1507_;
v___y_1450_ = v___x_1527_;
v___y_1451_ = v___x_1518_;
v___y_1452_ = v___x_1520_;
v_declId_1453_ = v_val_1577_;
goto v___jp_1447_;
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_val_1577_);
lean_dec_ref(v___x_1527_);
lean_dec(v_snd_1508_);
lean_dec(v_fst_1507_);
lean_dec(v_stx_1442_);
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_a_1591_);
lean_dec(v_val_1577_);
lean_dec_ref(v___x_1527_);
lean_dec(v_snd_1508_);
lean_dec(v_fst_1507_);
lean_dec(v_stx_1442_);
v_a_1619_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1599_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1599_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec(v_val_1577_);
lean_dec_ref(v___x_1527_);
lean_dec(v_snd_1508_);
lean_dec(v_fst_1507_);
lean_dec(v_stx_1442_);
v_a_1627_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1590_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1590_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_a_1498_);
lean_dec(v_a_1496_);
lean_dec(v_a_1469_);
lean_dec(v_stx_1442_);
lean_dec_ref(v_modifiers_1441_);
v_a_1638_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1499_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1499_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v_a_1496_);
lean_dec(v_a_1469_);
lean_dec(v_stx_1442_);
lean_dec_ref(v_modifiers_1441_);
v_a_1646_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1497_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1497_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v_a_1469_);
lean_dec(v_stx_1442_);
lean_dec_ref(v_modifiers_1441_);
v_a_1654_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1495_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1495_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
v___jp_1471_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1480_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0));
v___x_1481_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__1));
lean_inc_ref(v___y_1473_);
lean_inc_ref(v___y_1477_);
v___x_1482_ = l_Lean_Name_mkStr4(v___y_1477_, v___y_1473_, v___x_1480_, v___x_1481_);
v___x_1483_ = lean_unsigned_to_nat(1u);
v___x_1484_ = l_Lean_Syntax_getArg(v_stx_1442_, v___x_1483_);
v___x_1485_ = 1;
v___x_1486_ = l_Lean_mkIdentFrom(v___x_1484_, v___y_1475_, v___x_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = ((lean_object*)(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0));
lean_inc(v___y_1478_);
lean_inc_n(v___y_1479_, 2);
v___x_1488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1488_, 0, v___y_1479_);
lean_ctor_set(v___x_1488_, 1, v___y_1478_);
lean_ctor_set(v___x_1488_, 2, v___x_1487_);
v___x_1489_ = lean_mk_empty_array_with_capacity(v___x_1470_);
v___x_1490_ = lean_array_push(v___x_1489_, v___x_1486_);
v___x_1491_ = lean_array_push(v___x_1490_, v___x_1488_);
v___x_1492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1479_);
lean_ctor_set(v___x_1492_, 1, v___x_1482_);
lean_ctor_set(v___x_1492_, 2, v___x_1491_);
v___y_1448_ = v___y_1472_;
v___y_1449_ = v___y_1474_;
v___y_1450_ = v___y_1476_;
v___y_1451_ = v___y_1478_;
v___y_1452_ = v___y_1479_;
v_declId_1453_ = v___x_1492_;
goto v___jp_1447_;
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_stx_1442_);
lean_dec_ref(v_modifiers_1441_);
v_a_1662_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1468_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1468_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
v___jp_1447_:
{
lean_object* v_docString_x3f_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_docString_x3f_1454_ = lean_ctor_get(v___y_1450_, 1);
lean_inc(v_docString_x3f_1454_);
v___x_1455_ = 1;
v___x_1456_ = l_Lean_Syntax_getArgs(v_stx_1442_);
v___x_1457_ = lean_unsigned_to_nat(5u);
v___x_1458_ = l_Array_toSubarray___redArg(v___x_1456_, v___x_1446_, v___x_1457_);
v___x_1459_ = l_Subarray_copy___redArg(v___x_1458_);
v___x_1460_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1460_, 0, v___y_1452_);
lean_ctor_set(v___x_1460_, 1, v___y_1451_);
lean_ctor_set(v___x_1460_, 2, v___x_1459_);
v___x_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___y_1448_);
v___x_1462_ = l_Lean_Syntax_getArg(v_stx_1442_, v___x_1457_);
v___x_1463_ = lean_box(0);
v___x_1464_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1464_, 0, v_stx_1442_);
lean_ctor_set(v___x_1464_, 1, v___x_1460_);
lean_ctor_set(v___x_1464_, 2, v___y_1450_);
lean_ctor_set(v___x_1464_, 3, v_declId_1453_);
lean_ctor_set(v___x_1464_, 4, v___y_1449_);
lean_ctor_set(v___x_1464_, 5, v___x_1461_);
lean_ctor_set(v___x_1464_, 6, v___x_1462_);
lean_ctor_set(v___x_1464_, 7, v_docString_x3f_1454_);
lean_ctor_set(v___x_1464_, 8, v___x_1463_);
lean_ctor_set(v___x_1464_, 9, v___x_1463_);
lean_ctor_set_uint8(v___x_1464_, sizeof(void*)*10, v___x_1455_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object* v_modifiers_1670_, lean_object* v_stx_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Elab_Command_mkDefViewOfInstance(v_modifiers_1670_, v_stx_1671_, v_a_1672_, v_a_1673_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(lean_object* v_00_u03b1_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_1677_, v___y_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1681_, lean_object* v_x_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(v_00_u03b1_1681_, v_x_1682_, v___y_1683_, v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec_ref(v_x_1682_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(lean_object* v_00_u03b1_1686_, lean_object* v_ref_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_1687_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1692_, lean_object* v_ref_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(v_00_u03b1_1692_, v_ref_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(lean_object* v_00_u03b1_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(v_00_u03b1_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(lean_object* v_00_u03b1_1708_, lean_object* v_x_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v_x_1709_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___boxed(lean_object* v_00_u03b1_1714_, lean_object* v_x_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(v_00_u03b1_1714_, v_x_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(lean_object* v_msgData_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_1720_, v___y_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___boxed(lean_object* v_msgData_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(v_msgData_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(lean_object* v_as_1730_, lean_object* v_as_x27_1731_, lean_object* v_b_1732_, lean_object* v_a_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_1731_, v_b_1732_, v___y_1734_, v___y_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___boxed(lean_object* v_as_1738_, lean_object* v_as_x27_1739_, lean_object* v_b_1740_, lean_object* v_a_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(v_as_1738_, v_as_x27_1739_, v_b_1740_, v_a_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v_as_x27_1739_);
lean_dec(v_as_1738_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(lean_object* v_00_u03b1_1746_, lean_object* v_ref_1747_, lean_object* v_msg_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_1747_, v_msg_1748_, v___y_1749_, v___y_1750_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1753_, lean_object* v_ref_1754_, lean_object* v_msg_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(v_00_u03b1_1753_, v_ref_1754_, v_msg_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v_ref_1754_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1760_, lean_object* v_m_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_1761_, v_a_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_1764_, lean_object* v_m_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(v_00_u03b2_1764_, v_m_1765_, v_a_1766_);
lean_dec(v_a_1766_);
lean_dec_ref(v_m_1765_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(lean_object* v_00_u03b1_1768_, lean_object* v_msg_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1769_, v___y_1770_, v___y_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_msg_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(v_00_u03b1_1774_, v_msg_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
return v_res_1779_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
uint8_t v___x_1783_; 
v___x_1783_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_1781_, v_x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1784_, lean_object* v_x_1785_, lean_object* v_x_1786_){
_start:
{
uint8_t v_res_1787_; lean_object* v_r_1788_; 
v_res_1787_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_1784_, v_x_1785_, v_x_1786_);
lean_dec_ref(v_x_1786_);
lean_dec_ref(v_x_1785_);
v_r_1788_ = lean_box(v_res_1787_);
return v_r_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1789_, lean_object* v_a_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_1790_, v_x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1793_, lean_object* v_a_1794_, lean_object* v_x_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(v_00_u03b2_1793_, v_a_1794_, v_x_1795_);
lean_dec(v_x_1795_);
lean_dec(v_a_1794_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(lean_object* v_msgData_1797_, lean_object* v_macroStack_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_1797_, v_macroStack_1798_, v___y_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___boxed(lean_object* v_msgData_1803_, lean_object* v_macroStack_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(v_msgData_1803_, v_macroStack_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
return v_res_1808_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_1809_, lean_object* v_x_1810_, size_t v_x_1811_, lean_object* v_x_1812_){
_start:
{
uint8_t v___x_1813_; 
v___x_1813_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_1810_, v_x_1811_, v_x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_){
_start:
{
size_t v_x_18691__boxed_1818_; uint8_t v_res_1819_; lean_object* v_r_1820_; 
v_x_18691__boxed_1818_ = lean_unbox_usize(v_x_1816_);
lean_dec(v_x_1816_);
v_res_1819_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_1814_, v_x_1815_, v_x_18691__boxed_1818_, v_x_1817_);
lean_dec_ref(v_x_1817_);
lean_dec_ref(v_x_1815_);
v_r_1820_ = lean_box(v_res_1819_);
return v_r_1820_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(lean_object* v_00_u03b2_1821_, lean_object* v_keys_1822_, lean_object* v_vals_1823_, lean_object* v_heq_1824_, lean_object* v_i_1825_, lean_object* v_k_1826_){
_start:
{
uint8_t v___x_1827_; 
v___x_1827_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_1822_, v_i_1825_, v_k_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___boxed(lean_object* v_00_u03b2_1828_, lean_object* v_keys_1829_, lean_object* v_vals_1830_, lean_object* v_heq_1831_, lean_object* v_i_1832_, lean_object* v_k_1833_){
_start:
{
uint8_t v_res_1834_; lean_object* v_r_1835_; 
v_res_1834_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(v_00_u03b2_1828_, v_keys_1829_, v_vals_1830_, v_heq_1831_, v_i_1832_, v_k_1833_);
lean_dec_ref(v_k_1833_);
lean_dec_ref(v_vals_1830_);
lean_dec_ref(v_keys_1829_);
v_r_1835_ = lean_box(v_res_1834_);
return v_r_1835_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6(void){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Array_mkArray0(lean_box(0));
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque(lean_object* v_modifiers_1860_, lean_object* v_stx_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v_fst_1868_; lean_object* v_snd_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1999_; 
v___x_1865_ = lean_unsigned_to_nat(2u);
v___x_1866_ = l_Lean_Syntax_getArg(v_stx_1861_, v___x_1865_);
v___x_1867_ = l_Lean_Elab_expandDeclSig(v___x_1866_);
lean_dec(v___x_1866_);
v_fst_1868_ = lean_ctor_get(v___x_1867_, 0);
v_snd_1869_ = lean_ctor_get(v___x_1867_, 1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1871_ = v___x_1867_;
v_isShared_1872_ = v_isSharedCheck_1999_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_snd_1869_);
lean_inc(v_fst_1868_);
lean_dec(v___x_1867_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1999_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v_val_1874_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v_val_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = lean_unsigned_to_nat(3u);
v___x_1933_ = l_Lean_Syntax_getArg(v_stx_1861_, v___x_1932_);
v___x_1934_ = l_Lean_Syntax_getOptional_x3f(v___x_1933_);
lean_dec(v___x_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
uint8_t v_isUnsafe_1935_; 
v_isUnsafe_1935_ = lean_ctor_get_uint8(v_modifiers_1860_, sizeof(void*)*3 + 4);
if (v_isUnsafe_1935_ == 0)
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_Elab_Command_getRef___redArg(v_a_1862_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1862_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_quotContext_x3f_1939_; lean_object* v___x_1940_; 
lean_dec_ref_known(v___x_1938_, 1);
v_quotContext_x3f_1939_ = lean_ctor_get(v_a_1862_, 5);
v___x_1940_ = l_Lean_SourceInfo_fromRef(v_a_1937_, v_isUnsafe_1935_);
lean_dec(v_a_1937_);
if (lean_obj_tag(v_quotContext_x3f_1939_) == 0)
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1863_);
lean_dec_ref(v___x_1949_);
goto v___jp_1941_;
}
else
{
goto v___jp_1941_;
}
v___jp_1941_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1942_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9));
v___x_1943_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10));
lean_inc_n(v___x_1940_, 2);
v___x_1944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1940_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1946_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6, &l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once, _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6);
v___x_1947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1940_);
lean_ctor_set(v___x_1947_, 1, v___x_1945_);
lean_ctor_set(v___x_1947_, 2, v___x_1946_);
v___x_1948_ = l_Lean_Syntax_node2(v___x_1940_, v___x_1942_, v___x_1944_, v___x_1947_);
v_val_1906_ = v___x_1948_;
v___y_1907_ = v_a_1862_;
v___y_1908_ = v_a_1863_;
goto v___jp_1905_;
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_a_1937_);
lean_del_object(v___x_1871_);
lean_dec(v_snd_1869_);
lean_dec(v_fst_1868_);
lean_dec(v_stx_1861_);
lean_dec_ref(v_modifiers_1860_);
v_a_1950_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1938_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1938_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_del_object(v___x_1871_);
lean_dec(v_snd_1869_);
lean_dec(v_fst_1868_);
lean_dec(v_stx_1861_);
lean_dec_ref(v_modifiers_1860_);
v_a_1958_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1936_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1936_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Elab_Command_getRef___redArg(v_a_1862_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v___x_1968_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1862_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_quotContext_x3f_1969_; uint8_t v___x_1970_; lean_object* v___x_1971_; 
lean_dec_ref_known(v___x_1968_, 1);
v_quotContext_x3f_1969_ = lean_ctor_get(v_a_1862_, 5);
v___x_1970_ = 0;
v___x_1971_ = l_Lean_SourceInfo_fromRef(v_a_1967_, v___x_1970_);
lean_dec(v_a_1967_);
if (lean_obj_tag(v_quotContext_x3f_1969_) == 0)
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1863_);
lean_dec_ref(v___x_1981_);
goto v___jp_1972_;
}
else
{
goto v___jp_1972_;
}
v___jp_1972_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1973_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9));
v___x_1974_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10));
lean_inc_n(v___x_1971_, 3);
v___x_1975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1971_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1977_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11));
v___x_1978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1971_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = l_Lean_Syntax_node1(v___x_1971_, v___x_1976_, v___x_1978_);
v___x_1980_ = l_Lean_Syntax_node2(v___x_1971_, v___x_1973_, v___x_1975_, v___x_1979_);
v_val_1906_ = v___x_1980_;
v___y_1907_ = v_a_1862_;
v___y_1908_ = v_a_1863_;
goto v___jp_1905_;
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec(v_a_1967_);
lean_del_object(v___x_1871_);
lean_dec(v_snd_1869_);
lean_dec(v_fst_1868_);
lean_dec(v_stx_1861_);
lean_dec_ref(v_modifiers_1860_);
v_a_1982_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1968_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1968_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_del_object(v___x_1871_);
lean_dec(v_snd_1869_);
lean_dec(v_fst_1868_);
lean_dec(v_stx_1861_);
lean_dec_ref(v_modifiers_1860_);
v_a_1990_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1966_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1966_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
else
{
lean_object* v_val_1998_; 
lean_del_object(v___x_1871_);
v_val_1998_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v___x_1934_, 1);
v_val_1874_ = v_val_1998_;
goto v___jp_1873_;
}
v___jp_1873_:
{
lean_object* v_docString_x3f_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_docString_x3f_1875_ = lean_ctor_get(v_modifiers_1860_, 1);
lean_inc(v_docString_x3f_1875_);
v___x_1876_ = 4;
v___x_1877_ = l_Lean_Syntax_getArgs(v_stx_1861_);
v___x_1878_ = lean_unsigned_to_nat(3u);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = l_Array_toSubarray___redArg(v___x_1877_, v___x_1879_, v___x_1878_);
v___x_1881_ = l_Subarray_copy___redArg(v___x_1880_);
v___x_1882_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1883_ = lean_box(2);
v___x_1884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v___x_1882_);
lean_ctor_set(v___x_1884_, 2, v___x_1881_);
v___x_1885_ = lean_unsigned_to_nat(1u);
v___x_1886_ = l_Lean_Syntax_getArg(v_stx_1861_, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_snd_1869_);
v___x_1888_ = lean_box(0);
v___x_1889_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1889_, 0, v_stx_1861_);
lean_ctor_set(v___x_1889_, 1, v___x_1884_);
lean_ctor_set(v___x_1889_, 2, v_modifiers_1860_);
lean_ctor_set(v___x_1889_, 3, v___x_1886_);
lean_ctor_set(v___x_1889_, 4, v_fst_1868_);
lean_ctor_set(v___x_1889_, 5, v___x_1887_);
lean_ctor_set(v___x_1889_, 6, v_val_1874_);
lean_ctor_set(v___x_1889_, 7, v_docString_x3f_1875_);
lean_ctor_set(v___x_1889_, 8, v___x_1888_);
lean_ctor_set(v___x_1889_, 9, v___x_1888_);
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*10, v___x_1876_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
v___jp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1894_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1));
v___x_1895_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2));
lean_inc(v___y_1892_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 2);
lean_ctor_set(v___x_1871_, 1, v___x_1895_);
lean_ctor_set(v___x_1871_, 0, v___y_1892_);
v___x_1897_ = v___x_1871_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___y_1892_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1898_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5));
v___x_1899_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1900_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6, &l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once, _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6);
lean_inc_n(v___y_1892_, 2);
v___x_1901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1901_, 0, v___y_1892_);
lean_ctor_set(v___x_1901_, 1, v___x_1899_);
lean_ctor_set(v___x_1901_, 2, v___x_1900_);
lean_inc_ref_n(v___x_1901_, 2);
v___x_1902_ = l_Lean_Syntax_node2(v___y_1892_, v___x_1898_, v___x_1901_, v___x_1901_);
v___x_1903_ = l_Lean_Syntax_node4(v___y_1892_, v___x_1894_, v___x_1897_, v___y_1893_, v___x_1902_, v___x_1901_);
v_val_1874_ = v___x_1903_;
goto v___jp_1873_;
}
}
v___jp_1905_:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_Elab_Command_getRef___redArg(v___y_1907_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v___x_1911_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1907_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_quotContext_x3f_1912_; uint8_t v___x_1913_; lean_object* v___x_1914_; 
lean_dec_ref_known(v___x_1911_, 1);
v_quotContext_x3f_1912_ = lean_ctor_get(v___y_1907_, 5);
v___x_1913_ = 0;
v___x_1914_ = l_Lean_SourceInfo_fromRef(v_a_1910_, v___x_1913_);
lean_dec(v_a_1910_);
if (lean_obj_tag(v_quotContext_x3f_1912_) == 0)
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_1908_);
lean_dec_ref(v___x_1915_);
v___y_1892_ = v___x_1914_;
v___y_1893_ = v_val_1906_;
goto v___jp_1891_;
}
else
{
v___y_1892_ = v___x_1914_;
v___y_1893_ = v_val_1906_;
goto v___jp_1891_;
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1910_);
lean_dec(v_val_1906_);
lean_del_object(v___x_1871_);
lean_dec(v_snd_1869_);
lean_dec(v_fst_1868_);
lean_dec(v_stx_1861_);
lean_dec_ref(v_modifiers_1860_);
v_a_1916_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1911_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1911_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec(v_val_1906_);
lean_del_object(v___x_1871_);
lean_dec(v_snd_1869_);
lean_dec(v_fst_1868_);
lean_dec(v_stx_1861_);
lean_dec_ref(v_modifiers_1860_);
v_a_1924_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1909_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1909_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___boxed(lean_object* v_modifiers_2000_, lean_object* v_stx_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Elab_Command_mkDefViewOfOpaque(v_modifiers_2000_, v_stx_2001_, v_a_2002_, v_a_2003_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object* v_modifiers_2018_, lean_object* v_stx_2019_){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v_fst_2023_; lean_object* v_snd_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v_docString_x3f_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; lean_object* v_id_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2020_ = lean_unsigned_to_nat(1u);
v___x_2021_ = l_Lean_Syntax_getArg(v_stx_2019_, v___x_2020_);
v___x_2022_ = l_Lean_Elab_expandOptDeclSig(v___x_2021_);
lean_dec(v___x_2021_);
v_fst_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_fst_2023_);
v_snd_2024_ = lean_ctor_get(v___x_2022_, 1);
lean_inc(v_snd_2024_);
lean_dec_ref(v___x_2022_);
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_2027_ = lean_box(2);
v___x_2028_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__0));
v_docString_x3f_2029_ = lean_ctor_get(v_modifiers_2018_, 1);
lean_inc(v_docString_x3f_2029_);
v___x_2030_ = l_Lean_Syntax_getArg(v_stx_2019_, v___x_2025_);
v___x_2031_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__2));
v___x_2032_ = 1;
v_id_2033_ = l_Lean_mkIdentFrom(v___x_2030_, v___x_2031_, v___x_2032_);
lean_dec(v___x_2030_);
v___x_2034_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__3));
v___x_2035_ = lean_unsigned_to_nat(2u);
v___x_2036_ = lean_mk_empty_array_with_capacity(v___x_2035_);
v___x_2037_ = lean_array_push(v___x_2036_, v_id_2033_);
v___x_2038_ = lean_array_push(v___x_2037_, v___x_2028_);
v___x_2039_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2027_);
lean_ctor_set(v___x_2039_, 1, v___x_2034_);
lean_ctor_set(v___x_2039_, 2, v___x_2038_);
v___x_2040_ = 3;
v___x_2041_ = l_Lean_Syntax_getArgs(v_stx_2019_);
v___x_2042_ = l_Array_toSubarray___redArg(v___x_2041_, v___x_2025_, v___x_2035_);
v___x_2043_ = l_Subarray_copy___redArg(v___x_2042_);
v___x_2044_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2027_);
lean_ctor_set(v___x_2044_, 1, v___x_2026_);
lean_ctor_set(v___x_2044_, 2, v___x_2043_);
v___x_2045_ = l_Lean_Syntax_getArg(v_stx_2019_, v___x_2035_);
v___x_2046_ = lean_box(0);
v___x_2047_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2047_, 0, v_stx_2019_);
lean_ctor_set(v___x_2047_, 1, v___x_2044_);
lean_ctor_set(v___x_2047_, 2, v_modifiers_2018_);
lean_ctor_set(v___x_2047_, 3, v___x_2039_);
lean_ctor_set(v___x_2047_, 4, v_fst_2023_);
lean_ctor_set(v___x_2047_, 5, v_snd_2024_);
lean_ctor_set(v___x_2047_, 6, v___x_2045_);
lean_ctor_set(v___x_2047_, 7, v_docString_x3f_2029_);
lean_ctor_set(v___x_2047_, 8, v___x_2046_);
lean_ctor_set(v___x_2047_, 9, v___x_2046_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*10, v___x_2040_);
return v___x_2047_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_isDefLike(lean_object* v_stx_2083_){
_start:
{
lean_object* v_declKind_2084_; uint8_t v___y_2086_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
v_declKind_2084_ = l_Lean_Syntax_getKind(v_stx_2083_);
v___x_2095_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__8));
v___x_2096_ = lean_name_eq(v_declKind_2084_, v___x_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; uint8_t v___x_2098_; 
v___x_2097_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__10));
v___x_2098_ = lean_name_eq(v_declKind_2084_, v___x_2097_);
v___y_2086_ = v___x_2098_;
goto v___jp_2085_;
}
else
{
v___y_2086_ = v___x_2096_;
goto v___jp_2085_;
}
v___jp_2085_:
{
if (v___y_2086_ == 0)
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2088_ = lean_name_eq(v_declKind_2084_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__3));
v___x_2090_ = lean_name_eq(v_declKind_2084_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__4));
v___x_2092_ = lean_name_eq(v_declKind_2084_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2094_ = lean_name_eq(v_declKind_2084_, v___x_2093_);
lean_dec(v_declKind_2084_);
return v___x_2094_;
}
else
{
lean_dec(v_declKind_2084_);
return v___x_2092_;
}
}
else
{
lean_dec(v_declKind_2084_);
return v___x_2090_;
}
}
else
{
lean_dec(v_declKind_2084_);
return v___x_2088_;
}
}
else
{
lean_dec(v_declKind_2084_);
return v___y_2086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object* v_stx_2099_){
_start:
{
uint8_t v_res_2100_; lean_object* v_r_2101_; 
v_res_2100_ = l_Lean_Elab_Command_isDefLike(v_stx_2099_);
v_r_2101_ = lean_box(v_res_2100_);
return v_r_2101_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefView___closed__1(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = ((lean_object*)(l_Lean_Elab_Command_mkDefView___closed__0));
v___x_2104_ = l_Lean_stringToMessageData(v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView(lean_object* v_modifiers_2105_, lean_object* v_stx_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_Elab_Command_getScope___redArg(v_a_2108_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2178_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2178_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2178_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v_stx_2115_; lean_object* v_docString_x3f_2116_; uint8_t v_visibility_2117_; uint8_t v_isProtected_2118_; uint8_t v_computeKind_2119_; uint8_t v_recKind_2120_; uint8_t v_isUnsafe_2121_; lean_object* v_attrs_2122_; lean_object* v_declKind_2123_; lean_object* v___y_2125_; uint8_t v___y_2159_; uint8_t v___x_2175_; uint8_t v___x_2176_; 
v_stx_2115_ = lean_ctor_get(v_modifiers_2105_, 0);
v_docString_x3f_2116_ = lean_ctor_get(v_modifiers_2105_, 1);
v_visibility_2117_ = lean_ctor_get_uint8(v_modifiers_2105_, sizeof(void*)*3);
v_isProtected_2118_ = lean_ctor_get_uint8(v_modifiers_2105_, sizeof(void*)*3 + 1);
v_computeKind_2119_ = lean_ctor_get_uint8(v_modifiers_2105_, sizeof(void*)*3 + 2);
v_recKind_2120_ = lean_ctor_get_uint8(v_modifiers_2105_, sizeof(void*)*3 + 3);
v_isUnsafe_2121_ = lean_ctor_get_uint8(v_modifiers_2105_, sizeof(void*)*3 + 4);
v_attrs_2122_ = lean_ctor_get(v_modifiers_2105_, 2);
lean_inc(v_stx_2106_);
v_declKind_2123_ = l_Lean_Syntax_getKind(v_stx_2106_);
v___x_2175_ = 0;
v___x_2176_ = l_Lean_Elab_instBEqComputeKind_beq(v_computeKind_2119_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_dec(v_a_2111_);
v___y_2159_ = v___x_2176_;
goto v___jp_2158_;
}
else
{
uint8_t v_isMeta_2177_; 
v_isMeta_2177_ = lean_ctor_get_uint8(v_a_2111_, sizeof(void*)*10 + 2);
lean_dec(v_a_2111_);
v___y_2159_ = v_isMeta_2177_;
goto v___jp_2158_;
}
v___jp_2124_:
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__8));
v___x_2127_ = lean_name_eq(v_declKind_2123_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2128_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__10));
v___x_2129_ = lean_name_eq(v_declKind_2123_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2131_ = lean_name_eq(v_declKind_2123_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__3));
v___x_2133_ = lean_name_eq(v_declKind_2123_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__4));
v___x_2135_ = lean_name_eq(v_declKind_2123_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2137_ = lean_name_eq(v_declKind_2123_, v___x_2136_);
lean_dec(v_declKind_2123_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec_ref(v___y_2125_);
lean_del_object(v___x_2113_);
lean_dec(v_stx_2106_);
v___x_2138_ = lean_obj_once(&l_Lean_Elab_Command_mkDefView___closed__1, &l_Lean_Elab_Command_mkDefView___closed__1_once, _init_l_Lean_Elab_Command_mkDefView___closed__1);
v___x_2139_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v___x_2138_, v_a_2107_, v_a_2108_);
return v___x_2139_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = l_Lean_Elab_Command_mkDefViewOfExample(v___y_2125_, v_stx_2106_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2140_);
v___x_2142_ = v___x_2113_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v___x_2144_; 
lean_dec(v_declKind_2123_);
lean_del_object(v___x_2113_);
v___x_2144_ = l_Lean_Elab_Command_mkDefViewOfInstance(v___y_2125_, v_stx_2106_, v_a_2107_, v_a_2108_);
return v___x_2144_;
}
}
else
{
lean_object* v___x_2145_; 
lean_dec(v_declKind_2123_);
lean_del_object(v___x_2113_);
v___x_2145_ = l_Lean_Elab_Command_mkDefViewOfOpaque(v___y_2125_, v_stx_2106_, v_a_2107_, v_a_2108_);
return v___x_2145_;
}
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_dec(v_declKind_2123_);
v___x_2146_ = l_Lean_Elab_Command_mkDefViewOfTheorem(v___y_2125_, v_stx_2106_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2146_);
v___x_2148_ = v___x_2113_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
lean_dec(v_declKind_2123_);
v___x_2150_ = l_Lean_Elab_Command_mkDefViewOfDef(v___y_2125_, v_stx_2106_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2150_);
v___x_2152_ = v___x_2113_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
lean_dec(v_declKind_2123_);
v___x_2154_ = l_Lean_Elab_Command_mkDefViewOfAbbrev(v___y_2125_, v_stx_2106_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2154_);
v___x_2156_ = v___x_2113_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
v___jp_2158_:
{
if (v___y_2159_ == 0)
{
v___y_2125_ = v_modifiers_2105_;
goto v___jp_2124_;
}
else
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2161_ = lean_name_eq(v_declKind_2123_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2163_ = lean_name_eq(v_declKind_2123_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2171_; 
lean_inc_ref(v_attrs_2122_);
lean_inc(v_docString_x3f_2116_);
lean_inc(v_stx_2115_);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_modifiers_2105_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; lean_object* v_unused_2173_; lean_object* v_unused_2174_; 
v_unused_2172_ = lean_ctor_get(v_modifiers_2105_, 2);
lean_dec(v_unused_2172_);
v_unused_2173_ = lean_ctor_get(v_modifiers_2105_, 1);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v_modifiers_2105_, 0);
lean_dec(v_unused_2174_);
v___x_2165_ = v_modifiers_2105_;
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
else
{
lean_dec(v_modifiers_2105_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
uint8_t v___x_2167_; lean_object* v___x_2169_; 
v___x_2167_ = 1;
if (v_isShared_2166_ == 0)
{
v___x_2169_ = v___x_2165_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_stx_2115_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_docString_x3f_2116_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_attrs_2122_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*3, v_visibility_2117_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*3 + 1, v_isProtected_2118_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*3 + 3, v_recKind_2120_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*3 + 4, v_isUnsafe_2121_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*3 + 2, v___x_2167_);
v___y_2125_ = v___x_2169_;
goto v___jp_2124_;
}
}
}
else
{
v___y_2125_ = v_modifiers_2105_;
goto v___jp_2124_;
}
}
else
{
v___y_2125_ = v_modifiers_2105_;
goto v___jp_2124_;
}
}
}
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_stx_2106_);
lean_dec_ref(v_modifiers_2105_);
v_a_2179_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2110_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2110_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object* v_modifiers_2187_, lean_object* v_stx_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Elab_Command_mkDefView(v_modifiers_2187_, v_stx_2188_, v_a_2189_, v_a_2190_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2254_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2255_ = 0;
v___x_2256_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2257_ = l_Lean_registerTraceClass(v___x_2254_, v___x_2255_, v___x_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2____boxed(lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_();
return v_res_2259_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_unsigned_to_nat(2390142386u);
v___x_2261_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2262_ = l_Lean_Name_num___override(v___x_2261_, v___x_2260_);
return v___x_2262_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2264_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2265_ = l_Lean_Name_str___override(v___x_2264_, v___x_2263_);
return v___x_2265_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2267_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2268_ = l_Lean_Name_str___override(v___x_2267_, v___x_2266_);
return v___x_2268_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = lean_unsigned_to_nat(2u);
v___x_2270_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2271_ = l_Lean_Name_num___override(v___x_2270_, v___x_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2273_; uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2273_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_2274_ = 0;
v___x_2275_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2276_ = l_Lean_registerTraceClass(v___x_2273_, v___x_2274_, v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2____boxed(lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_();
return v_res_2278_;
}
}
lean_object* runtime_initialize_Lean_Elab_DeclNameGen(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DeclUtil(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DefView(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_DeclNameGen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instInhabitedDefKind_default = _init_l_Lean_Elab_instInhabitedDefKind_default();
l_Lean_Elab_instInhabitedDefKind = _init_l_Lean_Elab_instInhabitedDefKind();
l_Lean_Elab_instInhabitedDefViewElabHeaderData_default = _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default);
l_Lean_Elab_instInhabitedDefViewElabHeaderData = _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData();
lean_mark_persistent(l_Lean_Elab_instInhabitedDefViewElabHeaderData);
l_Lean_Elab_instInhabitedDefView_default = _init_l_Lean_Elab_instInhabitedDefView_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedDefView_default);
l_Lean_Elab_instInhabitedDefView = _init_l_Lean_Elab_instInhabitedDefView();
lean_mark_persistent(l_Lean_Elab_instInhabitedDefView);
res = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DefView(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_DeclNameGen(uint8_t builtin);
lean_object* initialize_Lean_Elab_DeclUtil(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DefView(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_DeclNameGen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DefView(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DefView(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DefView(builtin);
}
#ifdef __cplusplus
}
#endif
