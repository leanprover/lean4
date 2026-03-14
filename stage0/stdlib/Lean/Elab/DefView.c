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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__19___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "generated "};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__7 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Command_mkDefViewOfInstance___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__8;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " for "};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__9 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Command_mkDefViewOfInstance___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__10;
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_tacSnap_x3f_176_);
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
lean_dec_ref(v_x_215_);
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
lean_dec_ref(v_tacSnap_x3f_219_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg(lean_object* v_cls_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_scopes_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_opts_483_; uint8_t v_hasTrace_484_; 
v___x_477_ = l_Lean_inheritedTraceOptions;
v___x_478_ = lean_st_ref_get(v___x_477_);
v___x_479_ = lean_st_ref_get(v___y_475_);
v_scopes_480_ = lean_ctor_get(v___x_479_, 2);
lean_inc(v_scopes_480_);
lean_dec(v___x_479_);
v___x_481_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_482_ = l_List_head_x21___redArg(v___x_481_, v_scopes_480_);
lean_dec(v_scopes_480_);
v_opts_483_ = lean_ctor_get(v___x_482_, 1);
lean_inc_ref(v_opts_483_);
lean_dec(v___x_482_);
v_hasTrace_484_ = lean_ctor_get_uint8(v_opts_483_, sizeof(void*)*1);
if (v_hasTrace_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec_ref(v_opts_483_);
lean_dec(v___x_478_);
lean_dec(v_cls_474_);
v___x_485_ = lean_box(v_hasTrace_484_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_487_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg___closed__1));
v___x_488_ = l_Lean_Name_append(v___x_487_, v_cls_474_);
v___x_489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_478_, v_opts_483_, v___x_488_);
lean_dec(v___x_488_);
lean_dec_ref(v_opts_483_);
lean_dec(v___x_478_);
v___x_490_ = lean_box(v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg___boxed(lean_object* v_cls_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg(v_cls_492_, v___y_493_);
lean_dec(v___y_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(lean_object* v_cls_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg(v_cls_496_, v___y_498_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___boxed(lean_object* v_cls_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_cls_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___redArg(lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; lean_object* v_env_509_; lean_object* v___x_510_; lean_object* v_mainModule_511_; lean_object* v___x_512_; 
v___x_508_ = lean_st_ref_get(v___y_506_);
v_env_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc_ref(v_env_509_);
lean_dec(v___x_508_);
v___x_510_ = l_Lean_Environment_header(v_env_509_);
lean_dec_ref(v_env_509_);
v_mainModule_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_mainModule_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v_mainModule_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___redArg___boxed(lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___redArg(v___y_513_);
lean_dec(v___y_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3(lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___redArg(v___y_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___boxed(lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3(v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_523_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = l_Lean_maxRecDepthErrorMessage;
v___x_530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3);
v___x_532_ = l_Lean_MessageData_ofFormat(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4);
v___x_534_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2));
v___x_535_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(lean_object* v_ref_536_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v_ref_536_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___boxed(lean_object* v_ref_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(lean_object* v_x_544_, lean_object* v___y_545_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; 
v_a_546_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_a_546_);
v___x_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_547_, 0, v_a_546_);
lean_ctor_set(v___x_547_, 1, v___y_545_);
return v___x_547_;
}
else
{
lean_object* v_a_548_; lean_object* v___x_549_; 
v_a_548_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_a_548_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_a_548_);
lean_ctor_set(v___x_549_, 1, v___y_545_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg___boxed(lean_object* v_x_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_550_, v___y_551_);
lean_dec_ref(v_x_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(lean_object* v_env_553_, lean_object* v_stx_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_553_, v_stx_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
if (lean_obj_tag(v_a_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_a_559_ = lean_ctor_get(v___x_557_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v___x_557_, 0);
lean_dec(v_unused_568_);
v___x_561_ = v___x_557_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_box(0);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_a_559_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v_val_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_597_; 
v_val_569_ = lean_ctor_get(v_a_558_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_a_558_);
if (v_isSharedCheck_597_ == 0)
{
v___x_571_ = v_a_558_;
v_isShared_572_ = v_isSharedCheck_597_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_val_569_);
lean_dec(v_a_558_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_597_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_snd_573_; 
v_snd_573_ = lean_ctor_get(v_val_569_, 1);
lean_inc(v_snd_573_);
lean_dec(v_val_569_);
if (lean_obj_tag(v_snd_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_583_; 
lean_del_object(v___x_571_);
v_a_574_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_a_574_);
lean_dec_ref(v___x_557_);
v_a_575_ = lean_ctor_get(v_snd_573_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_snd_573_);
if (v_isSharedCheck_583_ == 0)
{
v___x_577_ = v_snd_573_;
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v_snd_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_582_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; 
v___x_581_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_580_, v_a_574_);
lean_dec_ref(v___x_580_);
return v___x_581_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_596_; 
v_a_584_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_a_584_);
lean_dec_ref(v___x_557_);
v_a_585_ = lean_ctor_get(v_snd_573_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v_snd_573_);
if (v_isSharedCheck_596_ == 0)
{
v___x_587_ = v_snd_573_;
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v_snd_573_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_a_585_);
v___x_590_ = v___x_571_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_595_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_592_, v_a_584_);
lean_dec_ref(v___x_592_);
return v___x_593_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_a_598_ = lean_ctor_get(v___x_557_, 0);
v_a_599_ = lean_ctor_get(v___x_557_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_557_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_inc(v_a_598_);
lean_dec(v___x_557_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_598_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed(lean_object* v_env_607_, lean_object* v_stx_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(v_env_607_, v_stx_608_, v___y_609_, v___y_610_);
lean_dec_ref(v___y_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(lean_object* v_env_612_, lean_object* v_currNamespace_613_, lean_object* v_openDecls_614_, lean_object* v_n_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = l_Lean_ResolveName_resolveNamespace(v_env_612_, v_currNamespace_613_, v_openDecls_614_, v_n_615_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___y_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed(lean_object* v_env_620_, lean_object* v_currNamespace_621_, lean_object* v_openDecls_622_, lean_object* v_n_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(v_env_620_, v_currNamespace_621_, v_openDecls_622_, v_n_623_, v___y_624_, v___y_625_);
lean_dec_ref(v___y_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(lean_object* v_currNamespace_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v_currNamespace_627_);
lean_ctor_set(v___x_630_, 1, v___y_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(v_currNamespace_631_, v___y_632_, v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_634_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_box(0);
v___x_636_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg(){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0);
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___boxed(lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v_res_642_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17___redArg(lean_object* v_keys_643_, lean_object* v_i_644_, lean_object* v_k_645_){
_start:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_array_get_size(v_keys_643_);
v___x_647_ = lean_nat_dec_lt(v_i_644_, v___x_646_);
if (v___x_647_ == 0)
{
lean_dec(v_i_644_);
return v___x_647_;
}
else
{
lean_object* v_k_x27_648_; uint8_t v___x_649_; 
v_k_x27_648_ = lean_array_fget_borrowed(v_keys_643_, v_i_644_);
v___x_649_ = l_Lean_instBEqExtraModUse_beq(v_k_645_, v_k_x27_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = lean_nat_add(v_i_644_, v___x_650_);
lean_dec(v_i_644_);
v_i_644_ = v___x_651_;
goto _start;
}
else
{
lean_dec(v_i_644_);
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17___redArg___boxed(lean_object* v_keys_653_, lean_object* v_i_654_, lean_object* v_k_655_){
_start:
{
uint8_t v_res_656_; lean_object* v_r_657_; 
v_res_656_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17___redArg(v_keys_653_, v_i_654_, v_k_655_);
lean_dec_ref(v_k_655_);
lean_dec_ref(v_keys_653_);
v_r_657_ = lean_box(v_res_656_);
return v_r_657_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__0(void){
_start:
{
size_t v___x_658_; size_t v___x_659_; size_t v___x_660_; 
v___x_658_ = ((size_t)5ULL);
v___x_659_ = ((size_t)1ULL);
v___x_660_ = lean_usize_shift_left(v___x_659_, v___x_658_);
return v___x_660_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__1(void){
_start:
{
size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; 
v___x_661_ = ((size_t)1ULL);
v___x_662_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__0);
v___x_663_ = lean_usize_sub(v___x_662_, v___x_661_);
return v___x_663_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_x_664_, size_t v_x_665_, lean_object* v_x_666_){
_start:
{
if (lean_obj_tag(v_x_664_) == 0)
{
lean_object* v_es_667_; lean_object* v___x_668_; size_t v___x_669_; size_t v___x_670_; size_t v___x_671_; lean_object* v_j_672_; lean_object* v___x_673_; 
v_es_667_ = lean_ctor_get(v_x_664_, 0);
lean_inc_ref(v_es_667_);
lean_dec_ref(v_x_664_);
v___x_668_ = lean_box(2);
v___x_669_ = ((size_t)5ULL);
v___x_670_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___closed__1);
v___x_671_ = lean_usize_land(v_x_665_, v___x_670_);
v_j_672_ = lean_usize_to_nat(v___x_671_);
v___x_673_ = lean_array_get(v___x_668_, v_es_667_, v_j_672_);
lean_dec(v_j_672_);
lean_dec_ref(v_es_667_);
switch(lean_obj_tag(v___x_673_))
{
case 0:
{
lean_object* v_key_674_; uint8_t v___x_675_; 
v_key_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_key_674_);
lean_dec_ref(v___x_673_);
v___x_675_ = l_Lean_instBEqExtraModUse_beq(v_x_666_, v_key_674_);
lean_dec(v_key_674_);
return v___x_675_;
}
case 1:
{
lean_object* v_node_676_; size_t v___x_677_; 
v_node_676_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_node_676_);
lean_dec_ref(v___x_673_);
v___x_677_ = lean_usize_shift_right(v_x_665_, v___x_669_);
v_x_664_ = v_node_676_;
v_x_665_ = v___x_677_;
goto _start;
}
default: 
{
uint8_t v___x_679_; 
v___x_679_ = 0;
return v___x_679_;
}
}
}
else
{
lean_object* v_ks_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_ks_680_ = lean_ctor_get(v_x_664_, 0);
lean_inc_ref(v_ks_680_);
lean_dec_ref(v_x_664_);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17___redArg(v_ks_680_, v___x_681_, v_x_666_);
lean_dec_ref(v_ks_680_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg___boxed(lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
size_t v_x_14913__boxed_686_; uint8_t v_res_687_; lean_object* v_r_688_; 
v_x_14913__boxed_686_ = lean_unbox_usize(v_x_684_);
lean_dec(v_x_684_);
v_res_687_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg(v_x_683_, v_x_14913__boxed_686_, v_x_685_);
lean_dec_ref(v_x_685_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9___redArg(lean_object* v_x_689_, lean_object* v_x_690_){
_start:
{
uint64_t v___x_691_; size_t v___x_692_; uint8_t v___x_693_; 
v___x_691_ = l_Lean_instHashableExtraModUse_hash(v_x_690_);
v___x_692_ = lean_uint64_to_usize(v___x_691_);
v___x_693_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg(v_x_689_, v___x_692_, v_x_690_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9___redArg___boxed(lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9___redArg(v_x_694_, v_x_695_);
lean_dec_ref(v_x_695_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_698_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__0);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__1);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
lean_ctor_set(v___x_703_, 2, v___x_702_);
lean_ctor_set(v___x_703_, 3, v___x_701_);
lean_ctor_set(v___x_703_, 4, v___x_701_);
lean_ctor_set(v___x_703_, 5, v___x_701_);
lean_ctor_set(v___x_703_, 6, v___x_701_);
lean_ctor_set(v___x_703_, 7, v___x_701_);
lean_ctor_set(v___x_703_, 8, v___x_701_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_unsigned_to_nat(32u);
v___x_705_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_707_ = ((size_t)5ULL);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_unsigned_to_nat(32u);
v___x_710_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___x_711_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__3);
v___x_712_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_710_);
lean_ctor_set(v___x_712_, 2, v___x_708_);
lean_ctor_set(v___x_712_, 3, v___x_708_);
lean_ctor_set_usize(v___x_712_, 4, v___x_707_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_713_ = lean_box(1);
v___x_714_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__4);
v___x_715_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__1);
v___x_716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___x_714_);
lean_ctor_set(v___x_716_, 2, v___x_713_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg(lean_object* v_msgData_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; lean_object* v_env_721_; lean_object* v___x_722_; lean_object* v_scopes_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_opts_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_720_ = lean_st_ref_get(v___y_718_);
v_env_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc_ref(v_env_721_);
lean_dec(v___x_720_);
v___x_722_ = lean_st_ref_get(v___y_718_);
v_scopes_723_ = lean_ctor_get(v___x_722_, 2);
lean_inc(v_scopes_723_);
lean_dec(v___x_722_);
v___x_724_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_725_ = l_List_head_x21___redArg(v___x_724_, v_scopes_723_);
lean_dec(v_scopes_723_);
v_opts_726_ = lean_ctor_get(v___x_725_, 1);
lean_inc_ref(v_opts_726_);
lean_dec(v___x_725_);
v___x_727_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__2);
v___x_728_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___closed__5);
v___x_729_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_729_, 0, v_env_721_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
lean_ctor_set(v___x_729_, 2, v___x_728_);
lean_ctor_set(v___x_729_, 3, v_opts_726_);
v___x_730_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v_msgData_717_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg___boxed(lean_object* v_msgData_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg(v_msgData_732_, v___y_733_);
lean_dec(v___y_733_);
return v_res_735_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__0(void){
_start:
{
lean_object* v___x_736_; double v___x_737_; 
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_float_of_nat(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(lean_object* v_cls_741_, lean_object* v_msg_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Elab_Command_getRef___redArg(v___y_743_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_795_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref(v___x_746_);
v___x_748_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg(v_msg_742_, v___y_744_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_795_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_795_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_795_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v_traceState_754_; lean_object* v_env_755_; lean_object* v_messages_756_; lean_object* v_scopes_757_; lean_object* v_usedQuotCtxts_758_; lean_object* v_nextMacroScope_759_; lean_object* v_maxRecDepth_760_; lean_object* v_ngen_761_; lean_object* v_auxDeclNGen_762_; lean_object* v_infoState_763_; lean_object* v_snapshotTasks_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_794_; 
v___x_753_ = lean_st_ref_take(v___y_744_);
v_traceState_754_ = lean_ctor_get(v___x_753_, 9);
v_env_755_ = lean_ctor_get(v___x_753_, 0);
v_messages_756_ = lean_ctor_get(v___x_753_, 1);
v_scopes_757_ = lean_ctor_get(v___x_753_, 2);
v_usedQuotCtxts_758_ = lean_ctor_get(v___x_753_, 3);
v_nextMacroScope_759_ = lean_ctor_get(v___x_753_, 4);
v_maxRecDepth_760_ = lean_ctor_get(v___x_753_, 5);
v_ngen_761_ = lean_ctor_get(v___x_753_, 6);
v_auxDeclNGen_762_ = lean_ctor_get(v___x_753_, 7);
v_infoState_763_ = lean_ctor_get(v___x_753_, 8);
v_snapshotTasks_764_ = lean_ctor_get(v___x_753_, 10);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_794_ == 0)
{
v___x_766_ = v___x_753_;
v_isShared_767_ = v_isSharedCheck_794_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_snapshotTasks_764_);
lean_inc(v_traceState_754_);
lean_inc(v_infoState_763_);
lean_inc(v_auxDeclNGen_762_);
lean_inc(v_ngen_761_);
lean_inc(v_maxRecDepth_760_);
lean_inc(v_nextMacroScope_759_);
lean_inc(v_usedQuotCtxts_758_);
lean_inc(v_scopes_757_);
lean_inc(v_messages_756_);
lean_inc(v_env_755_);
lean_dec(v___x_753_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_794_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
uint64_t v_tid_768_; lean_object* v_traces_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_793_; 
v_tid_768_ = lean_ctor_get_uint64(v_traceState_754_, sizeof(void*)*1);
v_traces_769_ = lean_ctor_get(v_traceState_754_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v_traceState_754_);
if (v_isSharedCheck_793_ == 0)
{
v___x_771_ = v_traceState_754_;
v_isShared_772_ = v_isSharedCheck_793_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_traces_769_);
lean_dec(v_traceState_754_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_793_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; double v___x_774_; uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_773_ = lean_box(0);
v___x_774_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__0);
v___x_775_ = 0;
v___x_776_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__1));
v___x_777_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_777_, 0, v_cls_741_);
lean_ctor_set(v___x_777_, 1, v___x_773_);
lean_ctor_set(v___x_777_, 2, v___x_776_);
lean_ctor_set_float(v___x_777_, sizeof(void*)*3, v___x_774_);
lean_ctor_set_float(v___x_777_, sizeof(void*)*3 + 8, v___x_774_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*3 + 16, v___x_775_);
v___x_778_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__2));
v___x_779_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set(v___x_779_, 1, v_a_749_);
lean_ctor_set(v___x_779_, 2, v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_a_747_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_PersistentArray_push___redArg(v_traces_769_, v___x_780_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_781_);
v___x_783_ = v___x_771_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_781_);
lean_ctor_set_uint64(v_reuseFailAlloc_792_, sizeof(void*)*1, v_tid_768_);
v___x_783_ = v_reuseFailAlloc_792_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 9, v___x_783_);
v___x_785_ = v___x_766_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_env_755_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_messages_756_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_scopes_757_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_usedQuotCtxts_758_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_nextMacroScope_759_);
lean_ctor_set(v_reuseFailAlloc_791_, 5, v_maxRecDepth_760_);
lean_ctor_set(v_reuseFailAlloc_791_, 6, v_ngen_761_);
lean_ctor_set(v_reuseFailAlloc_791_, 7, v_auxDeclNGen_762_);
lean_ctor_set(v_reuseFailAlloc_791_, 8, v_infoState_763_);
lean_ctor_set(v_reuseFailAlloc_791_, 9, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_791_, 10, v_snapshotTasks_764_);
v___x_785_ = v_reuseFailAlloc_791_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_786_ = lean_st_ref_set(v___y_744_, v___x_785_);
v___x_787_ = lean_box(0);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_787_);
v___x_789_ = v___x_751_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_msg_742_);
lean_dec(v_cls_741_);
v_a_796_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_746_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_746_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___boxed(lean_object* v_cls_804_, lean_object* v_msg_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(v_cls_804_, v_msg_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_809_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__2(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__1));
v___x_813_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__0));
v___x_814_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_813_, v___x_812_);
return v___x_814_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__5));
v___x_820_ = l_Lean_stringToMessageData(v___x_819_);
return v___x_820_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__8(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__7));
v___x_823_ = l_Lean_stringToMessageData(v___x_822_);
return v___x_823_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__9(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___closed__1));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__11(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__10));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__13(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__12));
v___x_831_ = l_Lean_stringToMessageData(v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(lean_object* v_mod_836_, uint8_t v_isMeta_837_, lean_object* v_hint_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; lean_object* v_env_843_; uint8_t v_isExporting_844_; lean_object* v___x_845_; lean_object* v_env_846_; lean_object* v___x_847_; lean_object* v_entry_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___y_853_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_842_ = lean_st_ref_get(v___y_840_);
v_env_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_env_843_);
lean_dec(v___x_842_);
v_isExporting_844_ = lean_ctor_get_uint8(v_env_843_, sizeof(void*)*8);
lean_dec_ref(v_env_843_);
v___x_845_ = lean_st_ref_get(v___y_840_);
v_env_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc_ref(v_env_846_);
lean_dec(v___x_845_);
v___x_847_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__2);
lean_inc(v_mod_836_);
v_entry_848_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_848_, 0, v_mod_836_);
lean_ctor_set_uint8(v_entry_848_, sizeof(void*)*1, v_isExporting_844_);
lean_ctor_set_uint8(v_entry_848_, sizeof(void*)*1 + 1, v_isMeta_837_);
v___x_849_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_850_ = lean_box(1);
v___x_851_ = lean_box(0);
v___x_879_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_847_, v___x_849_, v_env_846_, v___x_850_, v___x_851_);
v___x_880_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9___redArg(v___x_879_, v_entry_848_);
if (v___x_880_ == 0)
{
lean_object* v_cls_881_; lean_object* v___x_882_; lean_object* v_a_883_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_890_; lean_object* v___y_891_; uint8_t v___x_903_; 
v_cls_881_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__4));
v___x_882_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg(v_cls_881_, v___y_840_);
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v___x_882_);
v___x_903_ = lean_unbox(v_a_883_);
lean_dec(v_a_883_);
if (v___x_903_ == 0)
{
lean_dec(v_hint_838_);
lean_dec(v_mod_836_);
v___y_853_ = v___y_840_;
goto v___jp_852_;
}
else
{
lean_object* v___x_904_; lean_object* v___y_906_; 
v___x_904_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__11);
if (v_isExporting_844_ == 0)
{
lean_object* v___x_913_; 
v___x_913_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__16));
v___y_906_ = v___x_913_;
goto v___jp_905_;
}
else
{
lean_object* v___x_914_; 
v___x_914_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__17));
v___y_906_ = v___x_914_;
goto v___jp_905_;
}
v___jp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_907_ = l_Lean_stringToMessageData(v___y_906_);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_904_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__13);
v___x_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
if (v_isMeta_837_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__14));
v___y_890_ = v___x_910_;
v___y_891_ = v___x_911_;
goto v___jp_889_;
}
else
{
lean_object* v___x_912_; 
v___x_912_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__15));
v___y_890_ = v___x_910_;
v___y_891_ = v___x_912_;
goto v___jp_889_;
}
}
}
v___jp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___y_885_);
lean_ctor_set(v___x_887_, 1, v___y_886_);
v___x_888_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(v_cls_881_, v___x_887_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_dec_ref(v___x_888_);
v___y_853_ = v___y_840_;
goto v___jp_852_;
}
else
{
lean_dec_ref(v_entry_848_);
return v___x_888_;
}
}
v___jp_889_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_892_ = l_Lean_stringToMessageData(v___y_891_);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v___y_890_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__6);
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = l_Lean_MessageData_ofName(v_mod_836_);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l_Lean_Name_isAnonymous(v_hint_838_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__8);
v___x_900_ = l_Lean_MessageData_ofName(v_hint_838_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___y_885_ = v___x_897_;
v___y_886_ = v___x_901_;
goto v___jp_884_;
}
else
{
lean_object* v___x_902_; 
lean_dec(v_hint_838_);
v___x_902_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___closed__9);
v___y_885_ = v___x_897_;
v___y_886_ = v___x_902_;
goto v___jp_884_;
}
}
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec_ref(v_entry_848_);
lean_dec(v_hint_838_);
lean_dec(v_mod_836_);
v___x_915_ = lean_box(0);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
v___jp_852_:
{
lean_object* v___x_854_; lean_object* v_toEnvExtension_855_; lean_object* v_env_856_; lean_object* v_messages_857_; lean_object* v_scopes_858_; lean_object* v_usedQuotCtxts_859_; lean_object* v_nextMacroScope_860_; lean_object* v_maxRecDepth_861_; lean_object* v_ngen_862_; lean_object* v_auxDeclNGen_863_; lean_object* v_infoState_864_; lean_object* v_traceState_865_; lean_object* v_snapshotTasks_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_878_; 
v___x_854_ = lean_st_ref_take(v___y_853_);
v_toEnvExtension_855_ = lean_ctor_get(v___x_849_, 0);
lean_inc_ref(v_toEnvExtension_855_);
v_env_856_ = lean_ctor_get(v___x_854_, 0);
v_messages_857_ = lean_ctor_get(v___x_854_, 1);
v_scopes_858_ = lean_ctor_get(v___x_854_, 2);
v_usedQuotCtxts_859_ = lean_ctor_get(v___x_854_, 3);
v_nextMacroScope_860_ = lean_ctor_get(v___x_854_, 4);
v_maxRecDepth_861_ = lean_ctor_get(v___x_854_, 5);
v_ngen_862_ = lean_ctor_get(v___x_854_, 6);
v_auxDeclNGen_863_ = lean_ctor_get(v___x_854_, 7);
v_infoState_864_ = lean_ctor_get(v___x_854_, 8);
v_traceState_865_ = lean_ctor_get(v___x_854_, 9);
v_snapshotTasks_866_ = lean_ctor_get(v___x_854_, 10);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_878_ == 0)
{
v___x_868_ = v___x_854_;
v_isShared_869_ = v_isSharedCheck_878_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_snapshotTasks_866_);
lean_inc(v_traceState_865_);
lean_inc(v_infoState_864_);
lean_inc(v_auxDeclNGen_863_);
lean_inc(v_ngen_862_);
lean_inc(v_maxRecDepth_861_);
lean_inc(v_nextMacroScope_860_);
lean_inc(v_usedQuotCtxts_859_);
lean_inc(v_scopes_858_);
lean_inc(v_messages_857_);
lean_inc(v_env_856_);
lean_dec(v___x_854_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_878_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_asyncMode_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v_asyncMode_870_ = lean_ctor_get(v_toEnvExtension_855_, 2);
lean_inc(v_asyncMode_870_);
lean_dec_ref(v_toEnvExtension_855_);
v___x_871_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_849_, v_env_856_, v_entry_848_, v_asyncMode_870_, v___x_851_);
lean_dec(v_asyncMode_870_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_871_);
v___x_873_ = v___x_868_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_messages_857_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_scopes_858_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v_usedQuotCtxts_859_);
lean_ctor_set(v_reuseFailAlloc_877_, 4, v_nextMacroScope_860_);
lean_ctor_set(v_reuseFailAlloc_877_, 5, v_maxRecDepth_861_);
lean_ctor_set(v_reuseFailAlloc_877_, 6, v_ngen_862_);
lean_ctor_set(v_reuseFailAlloc_877_, 7, v_auxDeclNGen_863_);
lean_ctor_set(v_reuseFailAlloc_877_, 8, v_infoState_864_);
lean_ctor_set(v_reuseFailAlloc_877_, 9, v_traceState_865_);
lean_ctor_set(v_reuseFailAlloc_877_, 10, v_snapshotTasks_866_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_874_ = lean_st_ref_set(v___y_853_, v___x_873_);
v___x_875_ = lean_box(0);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___boxed(lean_object* v_mod_917_, lean_object* v_isMeta_918_, lean_object* v_hint_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
uint8_t v_isMeta_boxed_923_; lean_object* v_res_924_; 
v_isMeta_boxed_923_ = lean_unbox(v_isMeta_918_);
v_res_924_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v_mod_917_, v_isMeta_boxed_923_, v_hint_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(lean_object* v___x_925_, lean_object* v_declName_926_, lean_object* v_as_927_, size_t v_sz_928_, size_t v_i_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_dec(v_declName_926_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v_b_930_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; lean_object* v_modules_937_; lean_object* v___x_938_; lean_object* v_a_939_; lean_object* v___x_940_; lean_object* v_toImport_941_; lean_object* v_module_942_; uint8_t v___x_943_; lean_object* v___x_944_; 
v___x_936_ = l_Lean_Environment_header(v___x_925_);
v_modules_937_ = lean_ctor_get(v___x_936_, 3);
lean_inc_ref(v_modules_937_);
lean_dec_ref(v___x_936_);
v___x_938_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_939_ = lean_array_uget_borrowed(v_as_927_, v_i_929_);
v___x_940_ = lean_array_get(v___x_938_, v_modules_937_, v_a_939_);
lean_dec_ref(v_modules_937_);
v_toImport_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc_ref(v_toImport_941_);
lean_dec(v___x_940_);
v_module_942_ = lean_ctor_get(v_toImport_941_, 0);
lean_inc(v_module_942_);
lean_dec_ref(v_toImport_941_);
v___x_943_ = 0;
lean_inc(v_declName_926_);
v___x_944_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v_module_942_, v___x_943_, v_declName_926_, v___y_931_, v___y_932_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_945_; size_t v___x_946_; size_t v___x_947_; 
lean_dec_ref(v___x_944_);
v___x_945_ = lean_box(0);
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_add(v_i_929_, v___x_946_);
v_i_929_ = v___x_947_;
v_b_930_ = v___x_945_;
goto _start;
}
else
{
lean_dec(v_declName_926_);
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___boxed(lean_object* v___x_949_, lean_object* v_declName_950_, lean_object* v_as_951_, lean_object* v_sz_952_, lean_object* v_i_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
size_t v_sz_boxed_958_; size_t v_i_boxed_959_; lean_object* v_res_960_; 
v_sz_boxed_958_ = lean_unbox_usize(v_sz_952_);
lean_dec(v_sz_952_);
v_i_boxed_959_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_res_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(v___x_949_, v_declName_950_, v_as_951_, v_sz_boxed_958_, v_i_boxed_959_, v_b_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_as_951_);
lean_dec_ref(v___x_949_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12___redArg(lean_object* v_a_961_, lean_object* v_x_962_){
_start:
{
if (lean_obj_tag(v_x_962_) == 0)
{
lean_object* v___x_963_; 
v___x_963_ = lean_box(0);
return v___x_963_;
}
else
{
lean_object* v_key_964_; lean_object* v_value_965_; lean_object* v_tail_966_; uint8_t v___x_967_; 
v_key_964_ = lean_ctor_get(v_x_962_, 0);
v_value_965_ = lean_ctor_get(v_x_962_, 1);
v_tail_966_ = lean_ctor_get(v_x_962_, 2);
v___x_967_ = lean_name_eq(v_key_964_, v_a_961_);
if (v___x_967_ == 0)
{
v_x_962_ = v_tail_966_;
goto _start;
}
else
{
lean_object* v___x_969_; 
lean_inc(v_value_965_);
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v_value_965_);
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12___redArg___boxed(lean_object* v_a_970_, lean_object* v_x_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12___redArg(v_a_970_, v_x_971_);
lean_dec(v_x_971_);
lean_dec(v_a_970_);
return v_res_972_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_973_; uint64_t v___x_974_; 
v___x_973_ = lean_unsigned_to_nat(1723u);
v___x_974_ = lean_uint64_of_nat(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg(lean_object* v_m_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_buckets_977_; lean_object* v___x_978_; uint64_t v___y_980_; 
v_buckets_977_ = lean_ctor_get(v_m_975_, 1);
v___x_978_ = lean_array_get_size(v_buckets_977_);
if (lean_obj_tag(v_a_976_) == 0)
{
uint64_t v___x_994_; 
v___x_994_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg___closed__0);
v___y_980_ = v___x_994_;
goto v___jp_979_;
}
else
{
uint64_t v_hash_995_; 
v_hash_995_ = lean_ctor_get_uint64(v_a_976_, sizeof(void*)*2);
v___y_980_ = v_hash_995_;
goto v___jp_979_;
}
v___jp_979_:
{
uint64_t v___x_981_; uint64_t v___x_982_; uint64_t v_fold_983_; uint64_t v___x_984_; uint64_t v___x_985_; uint64_t v___x_986_; size_t v___x_987_; size_t v___x_988_; size_t v___x_989_; size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_981_ = 32ULL;
v___x_982_ = lean_uint64_shift_right(v___y_980_, v___x_981_);
v_fold_983_ = lean_uint64_xor(v___y_980_, v___x_982_);
v___x_984_ = 16ULL;
v___x_985_ = lean_uint64_shift_right(v_fold_983_, v___x_984_);
v___x_986_ = lean_uint64_xor(v_fold_983_, v___x_985_);
v___x_987_ = lean_uint64_to_usize(v___x_986_);
v___x_988_ = lean_usize_of_nat(v___x_978_);
v___x_989_ = ((size_t)1ULL);
v___x_990_ = lean_usize_sub(v___x_988_, v___x_989_);
v___x_991_ = lean_usize_land(v___x_987_, v___x_990_);
v___x_992_ = lean_array_uget_borrowed(v_buckets_977_, v___x_991_);
v___x_993_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12___redArg(v_a_976_, v___x_992_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_m_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg(v_m_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_m_996_);
return v_res_998_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1));
v___x_1002_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0));
v___x_1003_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(lean_object* v_declName_1006_, uint8_t v_isMeta_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v_env_1015_; lean_object* v___y_1017_; lean_object* v___x_1030_; 
v___x_1011_ = lean_st_ref_get(v___y_1009_);
v_env_1015_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_ref(v_env_1015_);
lean_dec(v___x_1011_);
v___x_1030_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1015_, v_declName_1006_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_dec_ref(v_env_1015_);
lean_dec(v_declName_1006_);
goto v___jp_1012_;
}
else
{
lean_object* v_val_1031_; lean_object* v___x_1032_; lean_object* v_modules_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_val_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_val_1031_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = l_Lean_Environment_header(v_env_1015_);
v_modules_1033_ = lean_ctor_get(v___x_1032_, 3);
lean_inc_ref(v_modules_1033_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = lean_array_get_size(v_modules_1033_);
v___x_1035_ = lean_nat_dec_lt(v_val_1031_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_dec_ref(v_modules_1033_);
lean_dec(v_val_1031_);
lean_dec_ref(v_env_1015_);
lean_dec(v_declName_1006_);
goto v___jp_1012_;
}
else
{
lean_object* v___x_1036_; lean_object* v_env_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___y_1041_; 
v___x_1036_ = lean_st_ref_get(v___y_1009_);
v_env_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc_ref(v_env_1037_);
lean_dec(v___x_1036_);
v___x_1038_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2);
v___x_1039_ = lean_array_fget(v_modules_1033_, v_val_1031_);
lean_dec(v_val_1031_);
lean_dec_ref(v_modules_1033_);
if (v_isMeta_1007_ == 0)
{
lean_dec_ref(v_env_1037_);
v___y_1041_ = v_isMeta_1007_;
goto v___jp_1040_;
}
else
{
uint8_t v___x_1052_; 
lean_inc(v_declName_1006_);
v___x_1052_ = l_Lean_isMarkedMeta(v_env_1037_, v_declName_1006_);
if (v___x_1052_ == 0)
{
v___y_1041_ = v_isMeta_1007_;
goto v___jp_1040_;
}
else
{
uint8_t v___x_1053_; 
v___x_1053_ = 0;
v___y_1041_ = v___x_1053_;
goto v___jp_1040_;
}
}
v___jp_1040_:
{
lean_object* v_toImport_1042_; lean_object* v_module_1043_; lean_object* v___x_1044_; 
v_toImport_1042_ = lean_ctor_get(v___x_1039_, 0);
lean_inc_ref(v_toImport_1042_);
lean_dec(v___x_1039_);
v_module_1043_ = lean_ctor_get(v_toImport_1042_, 0);
lean_inc(v_module_1043_);
lean_dec_ref(v_toImport_1042_);
lean_inc(v_declName_1006_);
v___x_1044_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v_module_1043_, v___y_1041_, v_declName_1006_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref(v___x_1044_);
v___x_1045_ = l_Lean_indirectModUseExt;
v___x_1046_ = lean_box(1);
v___x_1047_ = lean_box(0);
lean_inc_ref(v_env_1015_);
v___x_1048_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1038_, v___x_1045_, v_env_1015_, v___x_1046_, v___x_1047_);
v___x_1049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg(v___x_1048_, v_declName_1006_);
lean_dec(v___x_1048_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3));
v___y_1017_ = v___x_1050_;
goto v___jp_1016_;
}
else
{
lean_object* v_val_1051_; 
v_val_1051_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_val_1051_);
lean_dec_ref(v___x_1049_);
v___y_1017_ = v_val_1051_;
goto v___jp_1016_;
}
}
else
{
lean_dec_ref(v_env_1015_);
lean_dec(v_declName_1006_);
return v___x_1044_;
}
}
}
}
v___jp_1012_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
v___jp_1016_:
{
lean_object* v___x_1018_; size_t v_sz_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1018_ = lean_box(0);
v_sz_1019_ = lean_array_size(v___y_1017_);
v___x_1020_ = ((size_t)0ULL);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(v_env_1015_, v_declName_1006_, v___y_1017_, v_sz_1019_, v___x_1020_, v___x_1018_, v___y_1008_, v___y_1009_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_env_1015_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v___x_1021_, 0);
lean_dec(v_unused_1029_);
v___x_1023_ = v___x_1021_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_dec(v___x_1021_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1018_);
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1018_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
else
{
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___boxed(lean_object* v_declName_1054_, lean_object* v_isMeta_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
uint8_t v_isMeta_boxed_1059_; lean_object* v_res_1060_; 
v_isMeta_boxed_1059_ = lean_unbox(v_isMeta_1055_);
v_res_1060_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_declName_1054_, v_isMeta_boxed_1059_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(lean_object* v_as_x27_1061_, lean_object* v_b_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
if (lean_obj_tag(v_as_x27_1061_) == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_b_1062_);
return v___x_1066_;
}
else
{
lean_object* v_head_1067_; lean_object* v_tail_1068_; uint8_t v___x_1069_; lean_object* v___x_1070_; 
v_head_1067_ = lean_ctor_get(v_as_x27_1061_, 0);
lean_inc(v_head_1067_);
v_tail_1068_ = lean_ctor_get(v_as_x27_1061_, 1);
lean_inc(v_tail_1068_);
lean_dec_ref(v_as_x27_1061_);
v___x_1069_ = 1;
v___x_1070_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_head_1067_, v___x_1069_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v___x_1071_; 
lean_dec_ref(v___x_1070_);
v___x_1071_ = lean_box(0);
v_as_x27_1061_ = v_tail_1068_;
v_b_1062_ = v___x_1071_;
goto _start;
}
else
{
lean_dec(v_tail_1068_);
return v___x_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg___boxed(lean_object* v_as_x27_1073_, lean_object* v_b_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_1073_, v_b_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1078_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_box(1);
v___x_1080_ = l_Lean_MessageData_ofFormat(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__3(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__2));
v___x_1085_ = l_Lean_MessageData_ofFormat(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20(lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
if (lean_obj_tag(v_x_1087_) == 0)
{
return v_x_1086_;
}
else
{
lean_object* v_head_1088_; lean_object* v_tail_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1111_; 
v_head_1088_ = lean_ctor_get(v_x_1087_, 0);
v_tail_1089_ = lean_ctor_get(v_x_1087_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_x_1087_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1091_ = v_x_1087_;
v_isShared_1092_ = v_isSharedCheck_1111_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_tail_1089_);
lean_inc(v_head_1088_);
lean_dec(v_x_1087_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1111_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_before_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1109_; 
v_before_1093_ = lean_ctor_get(v_head_1088_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_head_1088_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v_head_1088_, 1);
lean_dec(v_unused_1110_);
v___x_1095_ = v_head_1088_;
v_isShared_1096_ = v_isSharedCheck_1109_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_before_1093_);
lean_dec(v_head_1088_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1109_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__0);
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 7);
lean_ctor_set(v___x_1095_, 1, v___x_1097_);
lean_ctor_set(v___x_1095_, 0, v_x_1086_);
v___x_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_x_1086_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1100_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__3);
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 7);
lean_ctor_set(v___x_1091_, 1, v___x_1100_);
lean_ctor_set(v___x_1091_, 0, v___x_1099_);
v___x_1102_ = v___x_1091_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = l_Lean_MessageData_ofSyntax(v_before_1093_);
v___x_1104_ = l_Lean_indentD(v___x_1103_);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1102_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v_x_1086_ = v___x_1105_;
v_x_1087_ = v_tail_1089_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__19(lean_object* v_opts_1112_, lean_object* v_opt_1113_){
_start:
{
lean_object* v_name_1114_; lean_object* v_defValue_1115_; lean_object* v_map_1116_; lean_object* v___x_1117_; 
v_name_1114_ = lean_ctor_get(v_opt_1113_, 0);
v_defValue_1115_ = lean_ctor_get(v_opt_1113_, 1);
v_map_1116_ = lean_ctor_get(v_opts_1112_, 0);
v___x_1117_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1116_, v_name_1114_);
if (lean_obj_tag(v___x_1117_) == 0)
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_unbox(v_defValue_1115_);
return v___x_1118_;
}
else
{
lean_object* v_val_1119_; 
v_val_1119_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_val_1119_);
lean_dec_ref(v___x_1117_);
if (lean_obj_tag(v_val_1119_) == 1)
{
uint8_t v_v_1120_; 
v_v_1120_ = lean_ctor_get_uint8(v_val_1119_, 0);
lean_dec_ref(v_val_1119_);
return v_v_1120_;
}
else
{
uint8_t v___x_1121_; 
lean_dec(v_val_1119_);
v___x_1121_ = lean_unbox(v_defValue_1115_);
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__19___boxed(lean_object* v_opts_1122_, lean_object* v_opt_1123_){
_start:
{
uint8_t v_res_1124_; lean_object* v_r_1125_; 
v_res_1124_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__19(v_opts_1122_, v_opt_1123_);
lean_dec_ref(v_opt_1123_);
lean_dec_ref(v_opts_1122_);
v_r_1125_ = lean_box(v_res_1124_);
return v_r_1125_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__2(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__1));
v___x_1130_ = l_Lean_MessageData_ofFormat(v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg(lean_object* v_msgData_1131_, lean_object* v_macroStack_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; lean_object* v_scopes_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v_opts_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1135_ = lean_st_ref_get(v___y_1133_);
v_scopes_1136_ = lean_ctor_get(v___x_1135_, 2);
lean_inc(v_scopes_1136_);
lean_dec(v___x_1135_);
v___x_1137_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1138_ = l_List_head_x21___redArg(v___x_1137_, v_scopes_1136_);
lean_dec(v_scopes_1136_);
v_opts_1139_ = lean_ctor_get(v___x_1138_, 1);
lean_inc_ref(v_opts_1139_);
lean_dec(v___x_1138_);
v___x_1140_ = l_Lean_Elab_pp_macroStack;
v___x_1141_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__19(v_opts_1139_, v___x_1140_);
lean_dec_ref(v_opts_1139_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
lean_dec(v_macroStack_1132_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_msgData_1131_);
return v___x_1142_;
}
else
{
if (lean_obj_tag(v_macroStack_1132_) == 0)
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_msgData_1131_);
return v___x_1143_;
}
else
{
lean_object* v_head_1144_; lean_object* v_after_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1160_; 
v_head_1144_ = lean_ctor_get(v_macroStack_1132_, 0);
lean_inc(v_head_1144_);
v_after_1145_ = lean_ctor_get(v_head_1144_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_head_1144_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v_head_1144_, 0);
lean_dec(v_unused_1161_);
v___x_1147_ = v_head_1144_;
v_isShared_1148_ = v_isSharedCheck_1160_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_after_1145_);
lean_dec(v_head_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1160_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20___closed__0);
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 7);
lean_ctor_set(v___x_1147_, 1, v___x_1149_);
lean_ctor_set(v___x_1147_, 0, v_msgData_1131_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_msgData_1131_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v_msgData_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1152_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___closed__2);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_MessageData_ofSyntax(v_after_1145_);
v___x_1155_ = l_Lean_indentD(v___x_1154_);
v_msgData_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1156_, 0, v___x_1153_);
lean_ctor_set(v_msgData_1156_, 1, v___x_1155_);
v___x_1157_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17_spec__20(v_msgData_1156_, v_macroStack_1132_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg___boxed(lean_object* v_msgData_1162_, lean_object* v_macroStack_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg(v_msgData_1162_, v_macroStack_1163_, v___y_1164_);
lean_dec(v___y_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10___redArg(lean_object* v_msg_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Elab_Command_getRef___redArg(v___y_1168_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v_macroStack_1173_; lean_object* v___x_1174_; lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1186_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref(v___x_1171_);
v_macroStack_1173_ = lean_ctor_get(v___y_1168_, 4);
lean_inc(v_macroStack_1173_);
lean_dec_ref(v___y_1168_);
v___x_1174_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg(v_msg_1167_, v___y_1169_);
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___x_1174_);
lean_inc(v_macroStack_1173_);
v___x_1176_ = l_Lean_Elab_getBetterRef(v_a_1172_, v_macroStack_1173_);
lean_dec(v_a_1172_);
v___x_1177_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg(v_a_1175_, v_macroStack_1173_, v___y_1169_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1176_);
lean_ctor_set(v___x_1182_, 1, v_a_1178_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set_tag(v___x_1180_, 1);
lean_ctor_set(v___x_1180_, 0, v___x_1182_);
v___x_1184_ = v___x_1180_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v___y_1168_);
lean_dec_ref(v_msg_1167_);
v_a_1187_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1171_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1171_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_msg_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10___redArg(v_msg_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(lean_object* v_ref_1200_, lean_object* v_msg_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_Elab_Command_getRef___redArg(v___y_1202_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v_fileName_1207_; lean_object* v_fileMap_1208_; lean_object* v_currRecDepth_1209_; lean_object* v_cmdPos_1210_; lean_object* v_macroStack_1211_; lean_object* v_quotContext_x3f_1212_; lean_object* v_currMacroScope_1213_; lean_object* v_snap_x3f_1214_; lean_object* v_cancelTk_x3f_1215_; uint8_t v_suppressElabErrors_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1225_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref(v___x_1205_);
v_fileName_1207_ = lean_ctor_get(v___y_1202_, 0);
v_fileMap_1208_ = lean_ctor_get(v___y_1202_, 1);
v_currRecDepth_1209_ = lean_ctor_get(v___y_1202_, 2);
v_cmdPos_1210_ = lean_ctor_get(v___y_1202_, 3);
v_macroStack_1211_ = lean_ctor_get(v___y_1202_, 4);
v_quotContext_x3f_1212_ = lean_ctor_get(v___y_1202_, 5);
v_currMacroScope_1213_ = lean_ctor_get(v___y_1202_, 6);
v_snap_x3f_1214_ = lean_ctor_get(v___y_1202_, 8);
v_cancelTk_x3f_1215_ = lean_ctor_get(v___y_1202_, 9);
v_suppressElabErrors_1216_ = lean_ctor_get_uint8(v___y_1202_, sizeof(void*)*10);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___y_1202_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___y_1202_, 7);
lean_dec(v_unused_1226_);
v___x_1218_ = v___y_1202_;
v_isShared_1219_ = v_isSharedCheck_1225_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_cancelTk_x3f_1215_);
lean_inc(v_snap_x3f_1214_);
lean_inc(v_currMacroScope_1213_);
lean_inc(v_quotContext_x3f_1212_);
lean_inc(v_macroStack_1211_);
lean_inc(v_cmdPos_1210_);
lean_inc(v_currRecDepth_1209_);
lean_inc(v_fileMap_1208_);
lean_inc(v_fileName_1207_);
lean_dec(v___y_1202_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1225_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v_ref_1220_; lean_object* v___x_1222_; 
v_ref_1220_ = l_Lean_replaceRef(v_ref_1200_, v_a_1206_);
lean_dec(v_a_1206_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 7, v_ref_1220_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_fileName_1207_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_fileMap_1208_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_currRecDepth_1209_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_cmdPos_1210_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_macroStack_1211_);
lean_ctor_set(v_reuseFailAlloc_1224_, 5, v_quotContext_x3f_1212_);
lean_ctor_set(v_reuseFailAlloc_1224_, 6, v_currMacroScope_1213_);
lean_ctor_set(v_reuseFailAlloc_1224_, 7, v_ref_1220_);
lean_ctor_set(v_reuseFailAlloc_1224_, 8, v_snap_x3f_1214_);
lean_ctor_set(v_reuseFailAlloc_1224_, 9, v_cancelTk_x3f_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1224_, sizeof(void*)*10, v_suppressElabErrors_1216_);
v___x_1222_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10___redArg(v_msg_1201_, v___x_1222_, v___y_1203_);
return v___x_1223_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec_ref(v___y_1202_);
lean_dec_ref(v_msg_1201_);
v_a_1227_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1205_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1205_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1235_, lean_object* v_msg_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_1235_, v_msg_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec(v_ref_1235_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(lean_object* v_env_1241_, lean_object* v_declName_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
uint8_t v___x_1245_; lean_object* v_env_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; uint8_t v___x_1249_; 
v___x_1245_ = 0;
v_env_1246_ = l_Lean_Environment_setExporting(v_env_1241_, v___x_1245_);
lean_inc(v_declName_1242_);
v___x_1247_ = l_Lean_mkPrivateName(v_env_1246_, v_declName_1242_);
v___x_1248_ = 1;
lean_inc_ref(v_env_1246_);
v___x_1249_ = l_Lean_Environment_contains(v_env_1246_, v___x_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1250_ = l_Lean_privateToUserName(v_declName_1242_);
v___x_1251_ = l_Lean_Environment_contains(v_env_1246_, v___x_1250_, v___x_1248_);
v___x_1252_ = lean_box(v___x_1251_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___y_1244_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec_ref(v_env_1246_);
lean_dec(v_declName_1242_);
v___x_1254_ = lean_box(v___x_1249_);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v___y_1244_);
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed(lean_object* v_env_1256_, lean_object* v_declName_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(v_env_1256_, v_declName_1257_, v___y_1258_, v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(lean_object* v_as_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
if (lean_obj_tag(v_as_1261_) == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
else
{
lean_object* v_head_1267_; lean_object* v_tail_1268_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v___x_1271_; lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1284_; 
v_head_1267_ = lean_ctor_get(v_as_1261_, 0);
lean_inc(v_head_1267_);
v_tail_1268_ = lean_ctor_get(v_as_1261_, 1);
lean_inc(v_tail_1268_);
lean_dec_ref(v_as_1261_);
v_fst_1269_ = lean_ctor_get(v_head_1267_, 0);
lean_inc(v_fst_1269_);
v_snd_1270_ = lean_ctor_get(v_head_1267_, 1);
lean_inc(v_snd_1270_);
lean_dec(v_head_1267_);
lean_inc(v_fst_1269_);
v___x_1271_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg(v_fst_1269_, v___y_1263_);
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1284_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1284_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
uint8_t v___x_1276_; 
v___x_1276_ = lean_unbox(v_a_1272_);
lean_dec(v_a_1272_);
if (v___x_1276_ == 0)
{
lean_del_object(v___x_1274_);
lean_dec(v_snd_1270_);
lean_dec(v_fst_1269_);
v_as_1261_ = v_tail_1268_;
goto _start;
}
else
{
lean_object* v___x_1279_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set_tag(v___x_1274_, 3);
lean_ctor_set(v___x_1274_, 0, v_snd_1270_);
v___x_1279_ = v___x_1274_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_snd_1270_);
v___x_1279_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = l_Lean_MessageData_ofFormat(v___x_1279_);
v___x_1281_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(v_fst_1269_, v___x_1280_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_dec_ref(v___x_1281_);
v_as_1261_ = v_tail_1268_;
goto _start;
}
else
{
lean_dec(v_tail_1268_);
return v___x_1281_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3___boxed(lean_object* v_as_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v_as_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(lean_object* v_env_1290_, lean_object* v_opts_1291_, lean_object* v_currNamespace_1292_, lean_object* v_openDecls_1293_, lean_object* v_n_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = l_Lean_ResolveName_resolveGlobalName(v_env_1290_, v_opts_1291_, v_currNamespace_1292_, v_openDecls_1293_, v_n_1294_);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v___y_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed(lean_object* v_env_1299_, lean_object* v_opts_1300_, lean_object* v_currNamespace_1301_, lean_object* v_openDecls_1302_, lean_object* v_n_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(v_env_1299_, v_opts_1300_, v_currNamespace_1301_, v_openDecls_1302_, v_n_1303_, v___y_1304_, v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec_ref(v_opts_1300_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(lean_object* v_x_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v_env_1313_; lean_object* v___x_1314_; lean_object* v_scopes_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_opts_1318_; lean_object* v___x_1319_; 
v___x_1312_ = lean_st_ref_get(v___y_1310_);
v_env_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_ref(v_env_1313_);
lean_dec(v___x_1312_);
v___x_1314_ = lean_st_ref_get(v___y_1310_);
v_scopes_1315_ = lean_ctor_get(v___x_1314_, 2);
lean_inc(v_scopes_1315_);
lean_dec(v___x_1314_);
v___x_1316_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1317_ = l_List_head_x21___redArg(v___x_1316_, v_scopes_1315_);
lean_dec(v_scopes_1315_);
v_opts_1318_ = lean_ctor_get(v___x_1317_, 1);
lean_inc_ref(v_opts_1318_);
lean_dec(v___x_1317_);
v___x_1319_ = l_Lean_Elab_Command_getScope___redArg(v___y_1310_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v_currNamespace_1321_; lean_object* v___x_1322_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1319_);
v_currNamespace_1321_ = lean_ctor_get(v_a_1320_, 2);
lean_inc(v_currNamespace_1321_);
lean_dec(v_a_1320_);
v___x_1322_ = l_Lean_Elab_Command_getScope___redArg(v___y_1310_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v_openDecls_1324_; lean_object* v___x_1325_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref(v___x_1322_);
v_openDecls_1324_ = lean_ctor_get(v_a_1323_, 3);
lean_inc(v_openDecls_1324_);
lean_dec(v_a_1323_);
v___x_1325_ = l_Lean_Elab_Command_getRef___redArg(v___y_1309_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1325_);
v___x_1327_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1309_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v_currRecDepth_1329_; lean_object* v_quotContext_x3f_1330_; lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___f_1333_; lean_object* v___f_1334_; lean_object* v___f_1335_; lean_object* v_methods_1336_; lean_object* v_a_1338_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref(v___x_1327_);
v_currRecDepth_1329_ = lean_ctor_get(v___y_1309_, 2);
v_quotContext_x3f_1330_ = lean_ctor_get(v___y_1309_, 5);
lean_inc_ref(v_env_1313_);
v___f_1331_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1331_, 0, v_env_1313_);
lean_inc_ref(v_env_1313_);
v___f_1332_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1332_, 0, v_env_1313_);
lean_inc(v_currNamespace_1321_);
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1333_, 0, v_currNamespace_1321_);
lean_inc(v_openDecls_1324_);
lean_inc(v_currNamespace_1321_);
lean_inc_ref(v_env_1313_);
v___f_1334_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1334_, 0, v_env_1313_);
lean_closure_set(v___f_1334_, 1, v_currNamespace_1321_);
lean_closure_set(v___f_1334_, 2, v_openDecls_1324_);
v___f_1335_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1335_, 0, v_env_1313_);
lean_closure_set(v___f_1335_, 1, v_opts_1318_);
lean_closure_set(v___f_1335_, 2, v_currNamespace_1321_);
lean_closure_set(v___f_1335_, 3, v_openDecls_1324_);
v_methods_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1336_, 0, v___f_1332_);
lean_ctor_set(v_methods_1336_, 1, v___f_1333_);
lean_ctor_set(v_methods_1336_, 2, v___f_1331_);
lean_ctor_set(v_methods_1336_, 3, v___f_1334_);
lean_ctor_set(v_methods_1336_, 4, v___f_1335_);
if (lean_obj_tag(v_quotContext_x3f_1330_) == 0)
{
lean_object* v___x_1410_; lean_object* v_a_1411_; 
v___x_1410_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___redArg(v___y_1310_);
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref(v___x_1410_);
v_a_1338_ = v_a_1411_;
goto v___jp_1337_;
}
else
{
lean_object* v_val_1412_; 
v_val_1412_ = lean_ctor_get(v_quotContext_x3f_1330_, 0);
lean_inc(v_val_1412_);
v_a_1338_ = v_val_1412_;
goto v___jp_1337_;
}
v___jp_1337_:
{
lean_object* v___x_1339_; lean_object* v_maxRecDepth_1340_; lean_object* v___x_1341_; lean_object* v_nextMacroScope_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1339_ = lean_st_ref_get(v___y_1310_);
v_maxRecDepth_1340_ = lean_ctor_get(v___x_1339_, 5);
lean_inc(v_maxRecDepth_1340_);
lean_dec(v___x_1339_);
v___x_1341_ = lean_st_ref_get(v___y_1310_);
v_nextMacroScope_1342_ = lean_ctor_get(v___x_1341_, 4);
lean_inc(v_nextMacroScope_1342_);
lean_dec(v___x_1341_);
lean_inc(v_currRecDepth_1329_);
v___x_1343_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1343_, 0, v_methods_1336_);
lean_ctor_set(v___x_1343_, 1, v_a_1338_);
lean_ctor_set(v___x_1343_, 2, v_a_1328_);
lean_ctor_set(v___x_1343_, 3, v_currRecDepth_1329_);
lean_ctor_set(v___x_1343_, 4, v_maxRecDepth_1340_);
lean_ctor_set(v___x_1343_, 5, v_a_1326_);
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1345_, 0, v_nextMacroScope_1342_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
lean_ctor_set(v___x_1345_, 2, v___x_1344_);
v___x_1346_ = lean_apply_2(v_x_1308_, v___x_1343_, v___x_1345_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v_a_1348_; lean_object* v_macroScope_1349_; lean_object* v_traceMsgs_1350_; lean_object* v_expandedMacroDecls_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 1);
lean_inc(v_a_1347_);
v_a_1348_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1346_);
v_macroScope_1349_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_macroScope_1349_);
v_traceMsgs_1350_ = lean_ctor_get(v_a_1347_, 1);
lean_inc(v_traceMsgs_1350_);
v_expandedMacroDecls_1351_ = lean_ctor_get(v_a_1347_, 2);
lean_inc(v_expandedMacroDecls_1351_);
lean_dec(v_a_1347_);
v___x_1352_ = lean_box(0);
v___x_1353_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_expandedMacroDecls_1351_, v___x_1352_, v___y_1309_, v___y_1310_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1354_; lean_object* v_env_1355_; lean_object* v_messages_1356_; lean_object* v_scopes_1357_; lean_object* v_usedQuotCtxts_1358_; lean_object* v_maxRecDepth_1359_; lean_object* v_ngen_1360_; lean_object* v_auxDeclNGen_1361_; lean_object* v_infoState_1362_; lean_object* v_traceState_1363_; lean_object* v_snapshotTasks_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v___x_1353_);
v___x_1354_ = lean_st_ref_take(v___y_1310_);
v_env_1355_ = lean_ctor_get(v___x_1354_, 0);
v_messages_1356_ = lean_ctor_get(v___x_1354_, 1);
v_scopes_1357_ = lean_ctor_get(v___x_1354_, 2);
v_usedQuotCtxts_1358_ = lean_ctor_get(v___x_1354_, 3);
v_maxRecDepth_1359_ = lean_ctor_get(v___x_1354_, 5);
v_ngen_1360_ = lean_ctor_get(v___x_1354_, 6);
v_auxDeclNGen_1361_ = lean_ctor_get(v___x_1354_, 7);
v_infoState_1362_ = lean_ctor_get(v___x_1354_, 8);
v_traceState_1363_ = lean_ctor_get(v___x_1354_, 9);
v_snapshotTasks_1364_ = lean_ctor_get(v___x_1354_, 10);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; 
v_unused_1391_ = lean_ctor_get(v___x_1354_, 4);
lean_dec(v_unused_1391_);
v___x_1366_ = v___x_1354_;
v_isShared_1367_ = v_isSharedCheck_1390_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_snapshotTasks_1364_);
lean_inc(v_traceState_1363_);
lean_inc(v_infoState_1362_);
lean_inc(v_auxDeclNGen_1361_);
lean_inc(v_ngen_1360_);
lean_inc(v_maxRecDepth_1359_);
lean_inc(v_usedQuotCtxts_1358_);
lean_inc(v_scopes_1357_);
lean_inc(v_messages_1356_);
lean_inc(v_env_1355_);
lean_dec(v___x_1354_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1390_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v_macroScope_1349_);
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_env_1355_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_messages_1356_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_scopes_1357_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_usedQuotCtxts_1358_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v_macroScope_1349_);
lean_ctor_set(v_reuseFailAlloc_1389_, 5, v_maxRecDepth_1359_);
lean_ctor_set(v_reuseFailAlloc_1389_, 6, v_ngen_1360_);
lean_ctor_set(v_reuseFailAlloc_1389_, 7, v_auxDeclNGen_1361_);
lean_ctor_set(v_reuseFailAlloc_1389_, 8, v_infoState_1362_);
lean_ctor_set(v_reuseFailAlloc_1389_, 9, v_traceState_1363_);
lean_ctor_set(v_reuseFailAlloc_1389_, 10, v_snapshotTasks_1364_);
v___x_1369_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1370_ = lean_st_ref_set(v___y_1310_, v___x_1369_);
v___x_1371_ = l_List_reverse___redArg(v_traceMsgs_1350_);
v___x_1372_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v___x_1371_, v___y_1309_, v___y_1310_);
lean_dec_ref(v___y_1309_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v___x_1372_, 0);
lean_dec(v_unused_1380_);
v___x_1374_ = v___x_1372_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v___x_1372_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v_a_1348_);
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1348_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_a_1348_);
v_a_1381_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1372_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1372_);
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
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec(v_traceMsgs_1350_);
lean_dec(v_macroScope_1349_);
lean_dec(v_a_1348_);
lean_dec_ref(v___y_1309_);
v_a_1392_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1353_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1353_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
lean_object* v_a_1400_; 
v_a_1400_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1400_);
lean_dec_ref(v___x_1346_);
if (lean_obj_tag(v_a_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v_a_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_a_1401_ = lean_ctor_get(v_a_1400_, 0);
lean_inc(v_a_1401_);
v_a_1402_ = lean_ctor_get(v_a_1400_, 1);
lean_inc_ref(v_a_1402_);
lean_dec_ref(v_a_1400_);
v___x_1403_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0));
v___x_1404_ = lean_string_dec_eq(v_a_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1405_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1405_, 0, v_a_1402_);
v___x_1406_ = l_Lean_MessageData_ofFormat(v___x_1405_);
v___x_1407_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_a_1401_, v___x_1406_, v___y_1309_, v___y_1310_);
lean_dec(v_a_1401_);
return v___x_1407_;
}
else
{
lean_object* v___x_1408_; 
lean_dec_ref(v_a_1402_);
lean_dec_ref(v___y_1309_);
v___x_1408_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_a_1401_);
return v___x_1408_;
}
}
else
{
lean_object* v___x_1409_; 
lean_dec_ref(v___y_1309_);
v___x_1409_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v___x_1409_;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_a_1326_);
lean_dec(v_openDecls_1324_);
lean_dec(v_currNamespace_1321_);
lean_dec_ref(v_opts_1318_);
lean_dec_ref(v_env_1313_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v_x_1308_);
v_a_1413_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1327_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1327_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_openDecls_1324_);
lean_dec(v_currNamespace_1321_);
lean_dec_ref(v_opts_1318_);
lean_dec_ref(v_env_1313_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v_x_1308_);
v_a_1421_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1325_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1325_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v_currNamespace_1321_);
lean_dec_ref(v_opts_1318_);
lean_dec_ref(v_env_1313_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v_x_1308_);
v_a_1429_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1322_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1322_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v_opts_1318_);
lean_dec_ref(v_env_1313_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v_x_1308_);
v_a_1437_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1319_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1319_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___boxed(lean_object* v_x_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v_x_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
return v_res_1449_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__8(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__7));
v___x_1466_ = l_Lean_stringToMessageData(v___x_1465_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__10(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__9));
v___x_1469_ = l_Lean_stringToMessageData(v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object* v_modifiers_1470_, lean_object* v_stx_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v___x_1475_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v_declId_1482_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1495_ = l_Lean_Syntax_getArg(v_stx_1471_, v___x_1475_);
v___x_1496_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_1496_, 0, v___x_1495_);
lean_inc_ref(v_a_1472_);
v___x_1497_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_1496_, v_a_1472_, v_a_1473_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref(v___x_1497_);
v___x_1499_ = lean_unsigned_to_nat(2u);
v___x_1522_ = l_Lean_Syntax_getArg(v_stx_1471_, v___x_1499_);
v___x_1523_ = lean_alloc_closure((void*)(l_Lean_Elab_expandOptNamedPrio___boxed), 3, 1);
lean_closure_set(v___x_1523_, 0, v___x_1522_);
lean_inc_ref(v_a_1472_);
v___x_1524_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_1523_, v_a_1472_, v_a_1473_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = l_Lean_Elab_Command_getRef___redArg(v_a_1472_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1526_);
v___x_1528_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1472_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_quotContext_x3f_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; 
lean_dec_ref(v___x_1528_);
v_quotContext_x3f_1529_ = lean_ctor_get(v_a_1472_, 5);
v___x_1530_ = 0;
v___x_1531_ = l_Lean_SourceInfo_fromRef(v_a_1527_, v___x_1530_);
lean_dec(v_a_1527_);
if (lean_obj_tag(v_quotContext_x3f_1529_) == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___redArg(v_a_1473_);
lean_dec_ref(v___x_1648_);
goto v___jp_1532_;
}
else
{
goto v___jp_1532_;
}
v___jp_1532_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v_fst_1536_; lean_object* v_snd_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1647_; 
v___x_1533_ = lean_unsigned_to_nat(4u);
v___x_1534_ = l_Lean_Syntax_getArg(v_stx_1471_, v___x_1533_);
v___x_1535_ = l_Lean_Elab_expandDeclSig(v___x_1534_);
lean_dec(v___x_1534_);
v_fst_1536_ = lean_ctor_get(v___x_1535_, 0);
v_snd_1537_ = lean_ctor_get(v___x_1535_, 1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1539_ = v___x_1535_;
v_isShared_1540_ = v_isSharedCheck_1647_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_snd_1537_);
lean_inc(v_fst_1536_);
lean_dec(v___x_1535_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1647_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1541_ = ((lean_object*)(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_));
v___x_1542_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2));
v___x_1543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0));
v___x_1544_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4));
lean_inc(v___x_1531_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 2);
lean_ctor_set(v___x_1539_, 1, v___x_1543_);
lean_ctor_set(v___x_1539_, 0, v___x_1531_);
v___x_1546_ = v___x_1539_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v___x_1543_);
v___x_1546_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1547_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1548_ = l_Nat_reprFast(v_a_1525_);
v___x_1549_ = lean_box(2);
v___x_1550_ = l_Lean_Syntax_mkNumLit(v___x_1548_, v___x_1549_);
lean_inc(v___x_1531_);
v___x_1551_ = l_Lean_Syntax_node1(v___x_1531_, v___x_1547_, v___x_1550_);
v___x_1552_ = l_Lean_Syntax_node2(v___x_1531_, v___x_1544_, v___x_1546_, v___x_1551_);
v___x_1553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1));
v___x_1554_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___x_1552_);
v___x_1555_ = lean_unbox(v_a_1498_);
lean_dec(v_a_1498_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*2, v___x_1555_);
v___x_1556_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_1470_, v___x_1554_);
v___x_1557_ = lean_unsigned_to_nat(3u);
v___x_1558_ = l_Lean_Syntax_getArg(v_stx_1471_, v___x_1557_);
v___x_1559_ = l_Lean_Syntax_getOptional_x3f(v___x_1558_);
lean_dec(v___x_1558_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = l_Lean_Syntax_getArgs(v_fst_1536_);
lean_inc_ref(v_a_1472_);
lean_inc(v_snd_1537_);
v___x_1561_ = l_Lean_Elab_Command_mkInstanceName(v___x_1560_, v_snd_1537_, v_a_1472_, v_a_1473_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_a_1565_; uint8_t v___x_1566_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1561_);
v___x_1563_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1564_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg(v___x_1563_, v_a_1473_);
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref(v___x_1564_);
v___x_1566_ = lean_unbox(v_a_1565_);
lean_dec(v_a_1565_);
if (v___x_1566_ == 0)
{
lean_dec_ref(v_a_1472_);
v___y_1501_ = v___x_1556_;
v___y_1502_ = v___x_1549_;
v___y_1503_ = v_a_1562_;
v___y_1504_ = v_fst_1536_;
v___y_1505_ = v___x_1547_;
v___y_1506_ = v_snd_1537_;
v___y_1507_ = v___x_1542_;
v___y_1508_ = v___x_1541_;
goto v___jp_1500_;
}
else
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Elab_Command_getScope___redArg(v_a_1473_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v_currNamespace_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1567_);
v_currNamespace_1569_ = lean_ctor_get(v_a_1568_, 2);
lean_inc(v_currNamespace_1569_);
lean_dec(v_a_1568_);
v___x_1570_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__8, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__8_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__8);
lean_inc(v_a_1562_);
v___x_1571_ = l_Lean_Name_append(v_currNamespace_1569_, v_a_1562_);
v___x_1572_ = l_Lean_MessageData_ofName(v___x_1571_);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1570_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(v___x_1563_, v___x_1573_, v_a_1472_, v_a_1473_);
lean_dec_ref(v_a_1472_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_dec_ref(v___x_1574_);
v___y_1501_ = v___x_1556_;
v___y_1502_ = v___x_1549_;
v___y_1503_ = v_a_1562_;
v___y_1504_ = v_fst_1536_;
v___y_1505_ = v___x_1547_;
v___y_1506_ = v_snd_1537_;
v___y_1507_ = v___x_1542_;
v___y_1508_ = v___x_1541_;
goto v___jp_1500_;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v_a_1562_);
lean_dec_ref(v___x_1556_);
lean_dec(v_snd_1537_);
lean_dec(v_fst_1536_);
lean_dec(v_stx_1471_);
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_a_1562_);
lean_dec_ref(v___x_1556_);
lean_dec(v_snd_1537_);
lean_dec(v_fst_1536_);
lean_dec_ref(v_a_1472_);
lean_dec(v_stx_1471_);
v_a_1583_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1567_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1567_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v___x_1556_);
lean_dec(v_snd_1537_);
lean_dec(v_fst_1536_);
lean_dec_ref(v_a_1472_);
lean_dec(v_stx_1471_);
v_a_1591_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1561_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1561_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v_val_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v_a_1602_; uint8_t v___x_1603_; 
v_val_1599_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_val_1599_);
lean_dec_ref(v___x_1559_);
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1601_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg(v___x_1600_, v_a_1473_);
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = lean_unbox(v_a_1602_);
lean_dec(v_a_1602_);
if (v___x_1603_ == 0)
{
lean_dec_ref(v_a_1472_);
v___y_1477_ = v___x_1556_;
v___y_1478_ = v___x_1549_;
v___y_1479_ = v_fst_1536_;
v___y_1480_ = v___x_1547_;
v___y_1481_ = v_snd_1537_;
v_declId_1482_ = v_val_1599_;
goto v___jp_1476_;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = l_Lean_Syntax_getArgs(v_fst_1536_);
lean_inc_ref(v_a_1472_);
lean_inc(v_snd_1537_);
v___x_1605_ = l_Lean_Elab_Command_mkInstanceName(v___x_1604_, v_snd_1537_, v_a_1472_, v_a_1473_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; lean_object* v_a_1608_; uint8_t v___x_1609_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref(v___x_1605_);
v___x_1607_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___redArg(v___x_1600_, v_a_1473_);
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref(v___x_1607_);
v___x_1609_ = lean_unbox(v_a_1608_);
lean_dec(v_a_1608_);
if (v___x_1609_ == 0)
{
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1472_);
v___y_1477_ = v___x_1556_;
v___y_1478_ = v___x_1549_;
v___y_1479_ = v_fst_1536_;
v___y_1480_ = v___x_1547_;
v___y_1481_ = v_snd_1537_;
v_declId_1482_ = v_val_1599_;
goto v___jp_1476_;
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Elab_Command_getScope___redArg(v_a_1473_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v_currNamespace_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v___x_1610_);
v_currNamespace_1612_ = lean_ctor_get(v_a_1611_, 2);
lean_inc(v_currNamespace_1612_);
lean_dec(v_a_1611_);
v___x_1613_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__8, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__8_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__8);
v___x_1614_ = l_Lean_Name_append(v_currNamespace_1612_, v_a_1606_);
v___x_1615_ = l_Lean_MessageData_ofName(v___x_1614_);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1613_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__10, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__10_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__10);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
lean_inc(v_val_1599_);
v___x_1619_ = l_Lean_MessageData_ofSyntax(v_val_1599_);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(v___x_1600_, v___x_1620_, v_a_1472_, v_a_1473_);
lean_dec_ref(v_a_1472_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_dec_ref(v___x_1621_);
v___y_1477_ = v___x_1556_;
v___y_1478_ = v___x_1549_;
v___y_1479_ = v_fst_1536_;
v___y_1480_ = v___x_1547_;
v___y_1481_ = v_snd_1537_;
v_declId_1482_ = v_val_1599_;
goto v___jp_1476_;
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_val_1599_);
lean_dec_ref(v___x_1556_);
lean_dec(v_snd_1537_);
lean_dec(v_fst_1536_);
lean_dec(v_stx_1471_);
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v_a_1606_);
lean_dec(v_val_1599_);
lean_dec_ref(v___x_1556_);
lean_dec(v_snd_1537_);
lean_dec(v_fst_1536_);
lean_dec_ref(v_a_1472_);
lean_dec(v_stx_1471_);
v_a_1630_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1610_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1610_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_val_1599_);
lean_dec_ref(v___x_1556_);
lean_dec(v_snd_1537_);
lean_dec(v_fst_1536_);
lean_dec_ref(v_a_1472_);
lean_dec(v_stx_1471_);
v_a_1638_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1605_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1605_);
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
}
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_a_1527_);
lean_dec(v_a_1525_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1472_);
lean_dec(v_stx_1471_);
lean_dec_ref(v_modifiers_1470_);
v_a_1649_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1528_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1528_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_a_1525_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1472_);
lean_dec(v_stx_1471_);
lean_dec_ref(v_modifiers_1470_);
v_a_1657_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1526_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1526_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1472_);
lean_dec(v_stx_1471_);
lean_dec_ref(v_modifiers_1470_);
v_a_1665_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1524_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1524_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
v___jp_1500_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1509_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0));
v___x_1510_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__1));
v___x_1511_ = l_Lean_Name_mkStr4(v___y_1508_, v___y_1507_, v___x_1509_, v___x_1510_);
v___x_1512_ = lean_unsigned_to_nat(1u);
v___x_1513_ = l_Lean_Syntax_getArg(v_stx_1471_, v___x_1512_);
v___x_1514_ = 1;
v___x_1515_ = l_Lean_mkIdentFrom(v___x_1513_, v___y_1503_, v___x_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = ((lean_object*)(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0));
lean_inc(v___y_1505_);
lean_inc(v___y_1502_);
v___x_1517_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1517_, 0, v___y_1502_);
lean_ctor_set(v___x_1517_, 1, v___y_1505_);
lean_ctor_set(v___x_1517_, 2, v___x_1516_);
v___x_1518_ = lean_mk_empty_array_with_capacity(v___x_1499_);
v___x_1519_ = lean_array_push(v___x_1518_, v___x_1515_);
v___x_1520_ = lean_array_push(v___x_1519_, v___x_1517_);
lean_inc(v___y_1502_);
v___x_1521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1521_, 0, v___y_1502_);
lean_ctor_set(v___x_1521_, 1, v___x_1511_);
lean_ctor_set(v___x_1521_, 2, v___x_1520_);
v___y_1477_ = v___y_1501_;
v___y_1478_ = v___y_1502_;
v___y_1479_ = v___y_1504_;
v___y_1480_ = v___y_1505_;
v___y_1481_ = v___y_1506_;
v_declId_1482_ = v___x_1521_;
goto v___jp_1476_;
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref(v_a_1472_);
lean_dec(v_stx_1471_);
lean_dec_ref(v_modifiers_1470_);
v_a_1673_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1497_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1497_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
v___jp_1476_:
{
lean_object* v_docString_x3f_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_docString_x3f_1483_ = lean_ctor_get(v___y_1477_, 1);
lean_inc(v_docString_x3f_1483_);
v___x_1484_ = 1;
v___x_1485_ = l_Lean_Syntax_getArgs(v_stx_1471_);
v___x_1486_ = lean_unsigned_to_nat(5u);
v___x_1487_ = l_Array_toSubarray___redArg(v___x_1485_, v___x_1475_, v___x_1486_);
v___x_1488_ = l_Subarray_copy___redArg(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1489_, 0, v___y_1478_);
lean_ctor_set(v___x_1489_, 1, v___y_1480_);
lean_ctor_set(v___x_1489_, 2, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1481_);
v___x_1491_ = l_Lean_Syntax_getArg(v_stx_1471_, v___x_1486_);
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1493_, 0, v_stx_1471_);
lean_ctor_set(v___x_1493_, 1, v___x_1489_);
lean_ctor_set(v___x_1493_, 2, v___y_1477_);
lean_ctor_set(v___x_1493_, 3, v_declId_1482_);
lean_ctor_set(v___x_1493_, 4, v___y_1479_);
lean_ctor_set(v___x_1493_, 5, v___x_1490_);
lean_ctor_set(v___x_1493_, 6, v___x_1491_);
lean_ctor_set(v___x_1493_, 7, v_docString_x3f_1483_);
lean_ctor_set(v___x_1493_, 8, v___x_1492_);
lean_ctor_set(v___x_1493_, 9, v___x_1492_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*10, v___x_1484_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object* v_modifiers_1681_, lean_object* v_stx_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_Elab_Command_mkDefViewOfInstance(v_modifiers_1681_, v_stx_1682_, v_a_1683_, v_a_1684_);
lean_dec(v_a_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(lean_object* v_00_u03b1_1687_, lean_object* v_x_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_1688_, v___y_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1692_, lean_object* v_x_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(v_00_u03b1_1692_, v_x_1693_, v___y_1694_, v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec_ref(v_x_1693_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(lean_object* v_00_u03b1_1697_, lean_object* v_ref_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_1698_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_ref_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(v_00_u03b1_1703_, v_ref_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(lean_object* v_00_u03b1_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(v_00_u03b1_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(lean_object* v_00_u03b1_1719_, lean_object* v_x_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v_x_1720_, v___y_1721_, v___y_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___boxed(lean_object* v_00_u03b1_1725_, lean_object* v_x_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(v_00_u03b1_1725_, v_x_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9(lean_object* v_msgData_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___redArg(v_msgData_1731_, v___y_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9___boxed(lean_object* v_msgData_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2_spec__9(v_msgData_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(lean_object* v_as_1741_, lean_object* v_as_x27_1742_, lean_object* v_b_1743_, lean_object* v_a_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_1742_, v_b_1743_, v___y_1745_, v___y_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___boxed(lean_object* v_as_1749_, lean_object* v_as_x27_1750_, lean_object* v_b_1751_, lean_object* v_a_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(v_as_1749_, v_as_x27_1750_, v_b_1751_, v_a_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v_as_1749_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(lean_object* v_00_u03b1_1757_, lean_object* v_ref_1758_, lean_object* v_msg_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_1758_, v_msg_1759_, v___y_1760_, v___y_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1764_, lean_object* v_ref_1765_, lean_object* v_msg_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(v_00_u03b1_1764_, v_ref_1765_, v_msg_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec(v_ref_1765_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_1771_, lean_object* v_m_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___redArg(v_m_1772_, v_a_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b2_1775_, lean_object* v_m_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6(v_00_u03b2_1775_, v_m_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_m_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10(lean_object* v_00_u03b1_1779_, lean_object* v_msg_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10___redArg(v_msg_1780_, v___y_1781_, v___y_1782_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b1_1785_, lean_object* v_msg_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10(v_00_u03b1_1785_, v_msg_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_){
_start:
{
uint8_t v___x_1794_; 
v___x_1794_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9___redArg(v_x_1792_, v_x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1795_, lean_object* v_x_1796_, lean_object* v_x_1797_){
_start:
{
uint8_t v_res_1798_; lean_object* v_r_1799_; 
v_res_1798_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9(v_00_u03b2_1795_, v_x_1796_, v_x_1797_);
lean_dec_ref(v_x_1797_);
v_r_1799_ = lean_box(v_res_1798_);
return v_r_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12(lean_object* v_00_u03b2_1800_, lean_object* v_a_1801_, lean_object* v_x_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12___redArg(v_a_1801_, v_x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1804_, lean_object* v_a_1805_, lean_object* v_x_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__6_spec__12(v_00_u03b2_1804_, v_a_1805_, v_x_1806_);
lean_dec(v_x_1806_);
lean_dec(v_a_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17(lean_object* v_msgData_1808_, lean_object* v_macroStack_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___redArg(v_msgData_1808_, v_macroStack_1809_, v___y_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17___boxed(lean_object* v_msgData_1814_, lean_object* v_macroStack_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10_spec__17(v_msgData_1814_, v_macroStack_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1819_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_1820_, lean_object* v_x_1821_, size_t v_x_1822_, lean_object* v_x_1823_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___redArg(v_x_1821_, v_x_1822_, v_x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13___boxed(lean_object* v_00_u03b2_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_){
_start:
{
size_t v_x_16810__boxed_1829_; uint8_t v_res_1830_; lean_object* v_r_1831_; 
v_x_16810__boxed_1829_ = lean_unbox_usize(v_x_1827_);
lean_dec(v_x_1827_);
v_res_1830_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13(v_00_u03b2_1825_, v_x_1826_, v_x_16810__boxed_1829_, v_x_1828_);
lean_dec_ref(v_x_1828_);
v_r_1831_ = lean_box(v_res_1830_);
return v_r_1831_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17(lean_object* v_00_u03b2_1832_, lean_object* v_keys_1833_, lean_object* v_vals_1834_, lean_object* v_heq_1835_, lean_object* v_i_1836_, lean_object* v_k_1837_){
_start:
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17___redArg(v_keys_1833_, v_i_1836_, v_k_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17___boxed(lean_object* v_00_u03b2_1839_, lean_object* v_keys_1840_, lean_object* v_vals_1841_, lean_object* v_heq_1842_, lean_object* v_i_1843_, lean_object* v_k_1844_){
_start:
{
uint8_t v_res_1845_; lean_object* v_r_1846_; 
v_res_1845_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4_spec__9_spec__13_spec__17(v_00_u03b2_1839_, v_keys_1840_, v_vals_1841_, v_heq_1842_, v_i_1843_, v_k_1844_);
lean_dec_ref(v_k_1844_);
lean_dec_ref(v_vals_1841_);
lean_dec_ref(v_keys_1840_);
v_r_1846_ = lean_box(v_res_1845_);
return v_r_1846_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6(void){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Array_mkArray0(lean_box(0));
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque(lean_object* v_modifiers_1871_, lean_object* v_stx_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v_fst_1879_; lean_object* v_snd_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_2010_; 
v___x_1876_ = lean_unsigned_to_nat(2u);
v___x_1877_ = l_Lean_Syntax_getArg(v_stx_1872_, v___x_1876_);
v___x_1878_ = l_Lean_Elab_expandDeclSig(v___x_1877_);
lean_dec(v___x_1877_);
v_fst_1879_ = lean_ctor_get(v___x_1878_, 0);
v_snd_1880_ = lean_ctor_get(v___x_1878_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1882_ = v___x_1878_;
v_isShared_1883_ = v_isSharedCheck_2010_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_snd_1880_);
lean_inc(v_fst_1879_);
lean_dec(v___x_1878_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_2010_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_val_1885_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v_val_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = lean_unsigned_to_nat(3u);
v___x_1944_ = l_Lean_Syntax_getArg(v_stx_1872_, v___x_1943_);
v___x_1945_ = l_Lean_Syntax_getOptional_x3f(v___x_1944_);
lean_dec(v___x_1944_);
if (lean_obj_tag(v___x_1945_) == 0)
{
uint8_t v_isUnsafe_1946_; 
v_isUnsafe_1946_ = lean_ctor_get_uint8(v_modifiers_1871_, sizeof(void*)*3 + 4);
if (v_isUnsafe_1946_ == 0)
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_Elab_Command_getRef___redArg(v_a_1873_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1949_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v___x_1949_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1873_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_quotContext_x3f_1950_; lean_object* v___x_1951_; 
lean_dec_ref(v___x_1949_);
v_quotContext_x3f_1950_ = lean_ctor_get(v_a_1873_, 5);
v___x_1951_ = l_Lean_SourceInfo_fromRef(v_a_1948_, v_isUnsafe_1946_);
lean_dec(v_a_1948_);
if (lean_obj_tag(v_quotContext_x3f_1950_) == 0)
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___redArg(v_a_1874_);
lean_dec_ref(v___x_1960_);
goto v___jp_1952_;
}
else
{
goto v___jp_1952_;
}
v___jp_1952_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1953_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9));
v___x_1954_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10));
lean_inc(v___x_1951_);
v___x_1955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1951_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1957_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6, &l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once, _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6);
lean_inc(v___x_1951_);
v___x_1958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1951_);
lean_ctor_set(v___x_1958_, 1, v___x_1956_);
lean_ctor_set(v___x_1958_, 2, v___x_1957_);
v___x_1959_ = l_Lean_Syntax_node2(v___x_1951_, v___x_1953_, v___x_1955_, v___x_1958_);
v_val_1917_ = v___x_1959_;
v___y_1918_ = v_a_1873_;
v___y_1919_ = v_a_1874_;
goto v___jp_1916_;
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v_a_1948_);
lean_del_object(v___x_1882_);
lean_dec(v_snd_1880_);
lean_dec(v_fst_1879_);
lean_dec(v_stx_1872_);
lean_dec_ref(v_modifiers_1871_);
v_a_1961_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1949_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1949_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_del_object(v___x_1882_);
lean_dec(v_snd_1880_);
lean_dec(v_fst_1879_);
lean_dec(v_stx_1872_);
lean_dec_ref(v_modifiers_1871_);
v_a_1969_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1947_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1947_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_Elab_Command_getRef___redArg(v_a_1873_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v___x_1977_);
v___x_1979_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1873_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_quotContext_x3f_1980_; uint8_t v___x_1981_; lean_object* v___x_1982_; 
lean_dec_ref(v___x_1979_);
v_quotContext_x3f_1980_ = lean_ctor_get(v_a_1873_, 5);
v___x_1981_ = 0;
v___x_1982_ = l_Lean_SourceInfo_fromRef(v_a_1978_, v___x_1981_);
lean_dec(v_a_1978_);
if (lean_obj_tag(v_quotContext_x3f_1980_) == 0)
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___redArg(v_a_1874_);
lean_dec_ref(v___x_1992_);
goto v___jp_1983_;
}
else
{
goto v___jp_1983_;
}
v___jp_1983_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1984_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9));
v___x_1985_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10));
lean_inc(v___x_1982_);
v___x_1986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1982_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1988_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11));
lean_inc(v___x_1982_);
v___x_1989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1982_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
lean_inc(v___x_1982_);
v___x_1990_ = l_Lean_Syntax_node1(v___x_1982_, v___x_1987_, v___x_1989_);
v___x_1991_ = l_Lean_Syntax_node2(v___x_1982_, v___x_1984_, v___x_1986_, v___x_1990_);
v_val_1917_ = v___x_1991_;
v___y_1918_ = v_a_1873_;
v___y_1919_ = v_a_1874_;
goto v___jp_1916_;
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec(v_a_1978_);
lean_del_object(v___x_1882_);
lean_dec(v_snd_1880_);
lean_dec(v_fst_1879_);
lean_dec(v_stx_1872_);
lean_dec_ref(v_modifiers_1871_);
v_a_1993_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1979_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1979_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_del_object(v___x_1882_);
lean_dec(v_snd_1880_);
lean_dec(v_fst_1879_);
lean_dec(v_stx_1872_);
lean_dec_ref(v_modifiers_1871_);
v_a_2001_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1977_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1977_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
else
{
lean_object* v_val_2009_; 
lean_del_object(v___x_1882_);
v_val_2009_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_val_2009_);
lean_dec_ref(v___x_1945_);
v_val_1885_ = v_val_2009_;
goto v___jp_1884_;
}
v___jp_1884_:
{
lean_object* v_docString_x3f_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_docString_x3f_1886_ = lean_ctor_get(v_modifiers_1871_, 1);
lean_inc(v_docString_x3f_1886_);
v___x_1887_ = 4;
v___x_1888_ = l_Lean_Syntax_getArgs(v_stx_1872_);
v___x_1889_ = lean_unsigned_to_nat(3u);
v___x_1890_ = lean_unsigned_to_nat(0u);
v___x_1891_ = l_Array_toSubarray___redArg(v___x_1888_, v___x_1890_, v___x_1889_);
v___x_1892_ = l_Subarray_copy___redArg(v___x_1891_);
v___x_1893_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1894_ = lean_box(2);
v___x_1895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v___x_1893_);
lean_ctor_set(v___x_1895_, 2, v___x_1892_);
v___x_1896_ = lean_unsigned_to_nat(1u);
v___x_1897_ = l_Lean_Syntax_getArg(v_stx_1872_, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_snd_1880_);
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1900_, 0, v_stx_1872_);
lean_ctor_set(v___x_1900_, 1, v___x_1895_);
lean_ctor_set(v___x_1900_, 2, v_modifiers_1871_);
lean_ctor_set(v___x_1900_, 3, v___x_1897_);
lean_ctor_set(v___x_1900_, 4, v_fst_1879_);
lean_ctor_set(v___x_1900_, 5, v___x_1898_);
lean_ctor_set(v___x_1900_, 6, v_val_1885_);
lean_ctor_set(v___x_1900_, 7, v_docString_x3f_1886_);
lean_ctor_set(v___x_1900_, 8, v___x_1899_);
lean_ctor_set(v___x_1900_, 9, v___x_1899_);
lean_ctor_set_uint8(v___x_1900_, sizeof(void*)*10, v___x_1887_);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
v___jp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1905_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1));
v___x_1906_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2));
lean_inc(v___y_1904_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 2);
lean_ctor_set(v___x_1882_, 1, v___x_1906_);
lean_ctor_set(v___x_1882_, 0, v___y_1904_);
v___x_1908_ = v___x_1882_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___y_1904_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1909_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5));
v___x_1910_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1911_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6, &l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once, _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6);
lean_inc(v___y_1904_);
v___x_1912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1912_, 0, v___y_1904_);
lean_ctor_set(v___x_1912_, 1, v___x_1910_);
lean_ctor_set(v___x_1912_, 2, v___x_1911_);
lean_inc_ref_n(v___x_1912_, 2);
lean_inc(v___y_1904_);
v___x_1913_ = l_Lean_Syntax_node2(v___y_1904_, v___x_1909_, v___x_1912_, v___x_1912_);
v___x_1914_ = l_Lean_Syntax_node4(v___y_1904_, v___x_1905_, v___x_1908_, v___y_1903_, v___x_1913_, v___x_1912_);
v_val_1885_ = v___x_1914_;
goto v___jp_1884_;
}
}
v___jp_1916_:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_Elab_Command_getRef___redArg(v___y_1918_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1920_);
v___x_1922_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1918_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_quotContext_x3f_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; 
lean_dec_ref(v___x_1922_);
v_quotContext_x3f_1923_ = lean_ctor_get(v___y_1918_, 5);
v___x_1924_ = 0;
v___x_1925_ = l_Lean_SourceInfo_fromRef(v_a_1921_, v___x_1924_);
lean_dec(v_a_1921_);
if (lean_obj_tag(v_quotContext_x3f_1923_) == 0)
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__3___redArg(v___y_1919_);
lean_dec_ref(v___x_1926_);
v___y_1903_ = v_val_1917_;
v___y_1904_ = v___x_1925_;
goto v___jp_1902_;
}
else
{
v___y_1903_ = v_val_1917_;
v___y_1904_ = v___x_1925_;
goto v___jp_1902_;
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec(v_a_1921_);
lean_dec(v_val_1917_);
lean_del_object(v___x_1882_);
lean_dec(v_snd_1880_);
lean_dec(v_fst_1879_);
lean_dec(v_stx_1872_);
lean_dec_ref(v_modifiers_1871_);
v_a_1927_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1922_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1922_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v_val_1917_);
lean_del_object(v___x_1882_);
lean_dec(v_snd_1880_);
lean_dec(v_fst_1879_);
lean_dec(v_stx_1872_);
lean_dec_ref(v_modifiers_1871_);
v_a_1935_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1920_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1920_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___boxed(lean_object* v_modifiers_2011_, lean_object* v_stx_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Elab_Command_mkDefViewOfOpaque(v_modifiers_2011_, v_stx_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object* v_modifiers_2029_, lean_object* v_stx_2030_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v_fst_2034_; lean_object* v_snd_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v_docString_x3f_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; lean_object* v_id_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2031_ = lean_unsigned_to_nat(1u);
v___x_2032_ = l_Lean_Syntax_getArg(v_stx_2030_, v___x_2031_);
v___x_2033_ = l_Lean_Elab_expandOptDeclSig(v___x_2032_);
lean_dec(v___x_2032_);
v_fst_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_fst_2034_);
v_snd_2035_ = lean_ctor_get(v___x_2033_, 1);
lean_inc(v_snd_2035_);
lean_dec_ref(v___x_2033_);
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_2038_ = lean_box(2);
v___x_2039_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__0));
v_docString_x3f_2040_ = lean_ctor_get(v_modifiers_2029_, 1);
lean_inc(v_docString_x3f_2040_);
v___x_2041_ = l_Lean_Syntax_getArg(v_stx_2030_, v___x_2036_);
v___x_2042_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__2));
v___x_2043_ = 1;
v_id_2044_ = l_Lean_mkIdentFrom(v___x_2041_, v___x_2042_, v___x_2043_);
lean_dec(v___x_2041_);
v___x_2045_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__3));
v___x_2046_ = lean_unsigned_to_nat(2u);
v___x_2047_ = lean_mk_empty_array_with_capacity(v___x_2046_);
v___x_2048_ = lean_array_push(v___x_2047_, v_id_2044_);
v___x_2049_ = lean_array_push(v___x_2048_, v___x_2039_);
v___x_2050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2038_);
lean_ctor_set(v___x_2050_, 1, v___x_2045_);
lean_ctor_set(v___x_2050_, 2, v___x_2049_);
v___x_2051_ = 3;
v___x_2052_ = l_Lean_Syntax_getArgs(v_stx_2030_);
v___x_2053_ = l_Array_toSubarray___redArg(v___x_2052_, v___x_2036_, v___x_2046_);
v___x_2054_ = l_Subarray_copy___redArg(v___x_2053_);
v___x_2055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2038_);
lean_ctor_set(v___x_2055_, 1, v___x_2037_);
lean_ctor_set(v___x_2055_, 2, v___x_2054_);
v___x_2056_ = l_Lean_Syntax_getArg(v_stx_2030_, v___x_2046_);
v___x_2057_ = lean_box(0);
v___x_2058_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2058_, 0, v_stx_2030_);
lean_ctor_set(v___x_2058_, 1, v___x_2055_);
lean_ctor_set(v___x_2058_, 2, v_modifiers_2029_);
lean_ctor_set(v___x_2058_, 3, v___x_2050_);
lean_ctor_set(v___x_2058_, 4, v_fst_2034_);
lean_ctor_set(v___x_2058_, 5, v_snd_2035_);
lean_ctor_set(v___x_2058_, 6, v___x_2056_);
lean_ctor_set(v___x_2058_, 7, v_docString_x3f_2040_);
lean_ctor_set(v___x_2058_, 8, v___x_2057_);
lean_ctor_set(v___x_2058_, 9, v___x_2057_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*10, v___x_2051_);
return v___x_2058_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_isDefLike(lean_object* v_stx_2094_){
_start:
{
lean_object* v_declKind_2095_; uint8_t v___y_2097_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v_declKind_2095_ = l_Lean_Syntax_getKind(v_stx_2094_);
v___x_2106_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__8));
v___x_2107_ = lean_name_eq(v_declKind_2095_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2108_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__10));
v___x_2109_ = lean_name_eq(v_declKind_2095_, v___x_2108_);
v___y_2097_ = v___x_2109_;
goto v___jp_2096_;
}
else
{
v___y_2097_ = v___x_2107_;
goto v___jp_2096_;
}
v___jp_2096_:
{
if (v___y_2097_ == 0)
{
lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2098_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2099_ = lean_name_eq(v_declKind_2095_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__3));
v___x_2101_ = lean_name_eq(v_declKind_2095_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__4));
v___x_2103_ = lean_name_eq(v_declKind_2095_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2104_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2105_ = lean_name_eq(v_declKind_2095_, v___x_2104_);
lean_dec(v_declKind_2095_);
return v___x_2105_;
}
else
{
lean_dec(v_declKind_2095_);
return v___x_2103_;
}
}
else
{
lean_dec(v_declKind_2095_);
return v___x_2101_;
}
}
else
{
lean_dec(v_declKind_2095_);
return v___x_2099_;
}
}
else
{
lean_dec(v_declKind_2095_);
return v___y_2097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object* v_stx_2110_){
_start:
{
uint8_t v_res_2111_; lean_object* v_r_2112_; 
v_res_2111_ = l_Lean_Elab_Command_isDefLike(v_stx_2110_);
v_r_2112_ = lean_box(v_res_2111_);
return v_r_2112_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefView___closed__1(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = ((lean_object*)(l_Lean_Elab_Command_mkDefView___closed__0));
v___x_2115_ = l_Lean_stringToMessageData(v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView(lean_object* v_modifiers_2116_, lean_object* v_stx_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Elab_Command_getScope___redArg(v_a_2119_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2189_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2189_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2189_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v_stx_2126_; lean_object* v_docString_x3f_2127_; uint8_t v_visibility_2128_; uint8_t v_isProtected_2129_; uint8_t v_computeKind_2130_; uint8_t v_recKind_2131_; uint8_t v_isUnsafe_2132_; lean_object* v_attrs_2133_; lean_object* v_declKind_2134_; lean_object* v___y_2136_; uint8_t v___y_2170_; uint8_t v___x_2186_; uint8_t v___x_2187_; 
v_stx_2126_ = lean_ctor_get(v_modifiers_2116_, 0);
v_docString_x3f_2127_ = lean_ctor_get(v_modifiers_2116_, 1);
v_visibility_2128_ = lean_ctor_get_uint8(v_modifiers_2116_, sizeof(void*)*3);
v_isProtected_2129_ = lean_ctor_get_uint8(v_modifiers_2116_, sizeof(void*)*3 + 1);
v_computeKind_2130_ = lean_ctor_get_uint8(v_modifiers_2116_, sizeof(void*)*3 + 2);
v_recKind_2131_ = lean_ctor_get_uint8(v_modifiers_2116_, sizeof(void*)*3 + 3);
v_isUnsafe_2132_ = lean_ctor_get_uint8(v_modifiers_2116_, sizeof(void*)*3 + 4);
v_attrs_2133_ = lean_ctor_get(v_modifiers_2116_, 2);
lean_inc(v_stx_2117_);
v_declKind_2134_ = l_Lean_Syntax_getKind(v_stx_2117_);
v___x_2186_ = 0;
v___x_2187_ = l_Lean_Elab_instBEqComputeKind_beq(v_computeKind_2130_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_dec(v_a_2122_);
v___y_2170_ = v___x_2187_;
goto v___jp_2169_;
}
else
{
uint8_t v_isMeta_2188_; 
v_isMeta_2188_ = lean_ctor_get_uint8(v_a_2122_, sizeof(void*)*10 + 2);
lean_dec(v_a_2122_);
v___y_2170_ = v_isMeta_2188_;
goto v___jp_2169_;
}
v___jp_2135_:
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__8));
v___x_2138_ = lean_name_eq(v_declKind_2134_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__10));
v___x_2140_ = lean_name_eq(v_declKind_2134_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2142_ = lean_name_eq(v_declKind_2134_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2143_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__3));
v___x_2144_ = lean_name_eq(v_declKind_2134_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2145_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__4));
v___x_2146_ = lean_name_eq(v_declKind_2134_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2147_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2148_ = lean_name_eq(v_declKind_2134_, v___x_2147_);
lean_dec(v_declKind_2134_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec_ref(v___y_2136_);
lean_del_object(v___x_2124_);
lean_dec(v_stx_2117_);
v___x_2149_ = lean_obj_once(&l_Lean_Elab_Command_mkDefView___closed__1, &l_Lean_Elab_Command_mkDefView___closed__1_once, _init_l_Lean_Elab_Command_mkDefView___closed__1);
v___x_2150_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__10___redArg(v___x_2149_, v_a_2118_, v_a_2119_);
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
lean_dec_ref(v_a_2118_);
v___x_2151_ = l_Lean_Elab_Command_mkDefViewOfExample(v___y_2136_, v_stx_2117_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2151_);
v___x_2153_ = v___x_2124_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
else
{
lean_object* v___x_2155_; 
lean_dec(v_declKind_2134_);
lean_del_object(v___x_2124_);
v___x_2155_ = l_Lean_Elab_Command_mkDefViewOfInstance(v___y_2136_, v_stx_2117_, v_a_2118_, v_a_2119_);
return v___x_2155_;
}
}
else
{
lean_object* v___x_2156_; 
lean_dec(v_declKind_2134_);
lean_del_object(v___x_2124_);
v___x_2156_ = l_Lean_Elab_Command_mkDefViewOfOpaque(v___y_2136_, v_stx_2117_, v_a_2118_, v_a_2119_);
lean_dec_ref(v_a_2118_);
return v___x_2156_;
}
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_dec(v_declKind_2134_);
lean_dec_ref(v_a_2118_);
v___x_2157_ = l_Lean_Elab_Command_mkDefViewOfTheorem(v___y_2136_, v_stx_2117_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2157_);
v___x_2159_ = v___x_2124_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
lean_dec(v_declKind_2134_);
lean_dec_ref(v_a_2118_);
v___x_2161_ = l_Lean_Elab_Command_mkDefViewOfDef(v___y_2136_, v_stx_2117_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2161_);
v___x_2163_ = v___x_2124_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_dec(v_declKind_2134_);
lean_dec_ref(v_a_2118_);
v___x_2165_ = l_Lean_Elab_Command_mkDefViewOfAbbrev(v___y_2136_, v_stx_2117_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2165_);
v___x_2167_ = v___x_2124_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
v___jp_2169_:
{
if (v___y_2170_ == 0)
{
v___y_2136_ = v_modifiers_2116_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2172_ = lean_name_eq(v_declKind_2134_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2174_ = lean_name_eq(v_declKind_2134_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2182_; 
lean_inc_ref(v_attrs_2133_);
lean_inc(v_docString_x3f_2127_);
lean_inc(v_stx_2126_);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_modifiers_2116_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; 
v_unused_2183_ = lean_ctor_get(v_modifiers_2116_, 2);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_modifiers_2116_, 1);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_modifiers_2116_, 0);
lean_dec(v_unused_2185_);
v___x_2176_ = v_modifiers_2116_;
v_isShared_2177_ = v_isSharedCheck_2182_;
goto v_resetjp_2175_;
}
else
{
lean_dec(v_modifiers_2116_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2182_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
uint8_t v___x_2178_; lean_object* v___x_2180_; 
v___x_2178_ = 1;
if (v_isShared_2177_ == 0)
{
v___x_2180_ = v___x_2176_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_stx_2126_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_docString_x3f_2127_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_attrs_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*3, v_visibility_2128_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*3 + 1, v_isProtected_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*3 + 3, v_recKind_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*3 + 4, v_isUnsafe_2132_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_ctor_set_uint8(v___x_2180_, sizeof(void*)*3 + 2, v___x_2178_);
v___y_2136_ = v___x_2180_;
goto v___jp_2135_;
}
}
}
else
{
v___y_2136_ = v_modifiers_2116_;
goto v___jp_2135_;
}
}
else
{
v___y_2136_ = v_modifiers_2116_;
goto v___jp_2135_;
}
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v_a_2118_);
lean_dec(v_stx_2117_);
lean_dec_ref(v_modifiers_2116_);
v_a_2190_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2121_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2121_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object* v_modifiers_2198_, lean_object* v_stx_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Elab_Command_mkDefView(v_modifiers_2198_, v_stx_2199_, v_a_2200_, v_a_2201_);
lean_dec(v_a_2201_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2265_; uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2265_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2266_ = 0;
v___x_2267_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2268_ = l_Lean_registerTraceClass(v___x_2265_, v___x_2266_, v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2____boxed(lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_();
return v_res_2270_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = lean_unsigned_to_nat(2390142386u);
v___x_2272_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2273_ = l_Lean_Name_num___override(v___x_2272_, v___x_2271_);
return v___x_2273_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2275_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2276_ = l_Lean_Name_str___override(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2278_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2279_ = l_Lean_Name_str___override(v___x_2278_, v___x_2277_);
return v___x_2279_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_unsigned_to_nat(2u);
v___x_2281_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2282_ = l_Lean_Name_num___override(v___x_2281_, v___x_2280_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2284_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_2285_ = 0;
v___x_2286_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2287_ = l_Lean_registerTraceClass(v___x_2284_, v___x_2285_, v___x_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2____boxed(lean_object* v_a_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_();
return v_res_2289_;
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
