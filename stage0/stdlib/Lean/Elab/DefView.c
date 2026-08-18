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
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Language_Snapshot_transform(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
extern lean_object* l_Lean_Elab_instInhabitedModifiers_default;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__1 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__1_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__2 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__2_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__3 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__3_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__4 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__4_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__5 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__5_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__6 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__6_value;
static const lean_ctor_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__1_value)}};
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__7 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__7_value;
static const lean_ctor_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__7_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__2_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__3_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__4_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__5_value)}};
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__8 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__8_value;
static const lean_ctor_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__8_value),((lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__6_value)}};
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__9 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__9_value;
static lean_once_cell_t l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_transform___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__11 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__11_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__11_value)} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__12 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__12_value;
static lean_once_cell_t l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value;
static const lean_closure_object l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value)} };
static const lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1 = (const lean_object*)&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1_value;
static lean_once_cell_t l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2;
static lean_once_cell_t l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot;
static const lean_string_object l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21_ = (const lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value;
static const lean_string_object l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21_ = (const lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value;
static const lean_string_object l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "DefsParsedSnapshot"};
static const lean_object* l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21_ = (const lean_object*)&l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value;
static const lean_ctor_object l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value_aux_0),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value_aux_1),((lean_object*)&l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(203, 62, 250, 36, 153, 122, 46, 61)}};
static const lean_object* l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21_ = (const lean_object*)&l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instImpl_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21_ = (const lean_object*)&l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instTypeNameDefsParsedSnapshot = (const lean_object*)&l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0;
static lean_once_cell_t l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1;
static lean_once_cell_t l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot;
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 1, 138, 227, 223, 112, 103, 179)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__4 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mkInstanceName"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__5 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Elab_Command_mkDefViewOfExample___closed__3 = (const lean_object*)&l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_isDefLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__0 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 116, 137, 74, 194, 103, 58, 54)}};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__1 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_isDefLike___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__2 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 217, 152, 21, 13, 97, 204, 102)}};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__3 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__4 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_isDefLike___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "example"};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__5 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__5_value),LEAN_SCALAR_PTR_LITERAL(108, 28, 224, 32, 144, 38, 51, 230)}};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__6 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_isDefLike___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "abbrev"};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__7 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__7_value),LEAN_SCALAR_PTR_LITERAL(34, 181, 25, 109, 89, 238, 86, 99)}};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__8 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_isDefLike___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Command_isDefLike___closed__9 = (const lean_object*)&l_Lean_Elab_Command_isDefLike___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_isDefLike___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Command_isDefLike___closed__9_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "DefView"};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 122, 8, 89, 37, 107, 94, 7)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(34, 72, 191, 5, 97, 231, 115, 233)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(3, 151, 93, 82, 32, 95, 13, 197)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(53, 155, 219, 87, 227, 165, 44, 167)}};
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
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(37, 248, 167, 23, 141, 24, 1, 218)}};
static const lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(19, 127, 79, 19, 22, 129, 157, 125)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___redArg(lean_object* v_k_11_){
_start:
{
lean_inc(v_k_11_);
return v_k_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___redArg___boxed(lean_object* v_k_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Elab_DefKind_ctorElim___redArg(v_k_12_);
lean_dec(v_k_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, uint8_t v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_inc(v_k_18_);
return v_k_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
uint8_t v_t_boxed_24_; lean_object* v_res_25_; 
v_t_boxed_24_ = lean_unbox(v_t_21_);
v_res_25_ = l_Lean_Elab_DefKind_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_boxed_24_, v_h_22_, v_k_23_);
lean_dec(v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___redArg(lean_object* v_def_26_){
_start:
{
lean_inc(v_def_26_);
return v_def_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___redArg___boxed(lean_object* v_def_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Elab_DefKind_def_elim___redArg(v_def_27_);
lean_dec(v_def_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim(lean_object* v_motive_29_, uint8_t v_t_30_, lean_object* v_h_31_, lean_object* v_def_32_){
_start:
{
lean_inc(v_def_32_);
return v_def_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___boxed(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_def_36_){
_start:
{
uint8_t v_t_boxed_37_; lean_object* v_res_38_; 
v_t_boxed_37_ = lean_unbox(v_t_34_);
v_res_38_ = l_Lean_Elab_DefKind_def_elim(v_motive_33_, v_t_boxed_37_, v_h_35_, v_def_36_);
lean_dec(v_def_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___redArg(lean_object* v_instance_39_){
_start:
{
lean_inc(v_instance_39_);
return v_instance_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___redArg___boxed(lean_object* v_instance_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Elab_DefKind_instance_elim___redArg(v_instance_40_);
lean_dec(v_instance_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim(lean_object* v_motive_42_, uint8_t v_t_43_, lean_object* v_h_44_, lean_object* v_instance_45_){
_start:
{
lean_inc(v_instance_45_);
return v_instance_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_instance_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Elab_DefKind_instance_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_instance_49_);
lean_dec(v_instance_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___redArg(lean_object* v_theorem_52_){
_start:
{
lean_inc(v_theorem_52_);
return v_theorem_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___redArg___boxed(lean_object* v_theorem_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Elab_DefKind_theorem_elim___redArg(v_theorem_53_);
lean_dec(v_theorem_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_theorem_58_){
_start:
{
lean_inc(v_theorem_58_);
return v_theorem_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___boxed(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_theorem_62_){
_start:
{
uint8_t v_t_boxed_63_; lean_object* v_res_64_; 
v_t_boxed_63_ = lean_unbox(v_t_60_);
v_res_64_ = l_Lean_Elab_DefKind_theorem_elim(v_motive_59_, v_t_boxed_63_, v_h_61_, v_theorem_62_);
lean_dec(v_theorem_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___redArg(lean_object* v_example_65_){
_start:
{
lean_inc(v_example_65_);
return v_example_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___redArg___boxed(lean_object* v_example_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Elab_DefKind_example_elim___redArg(v_example_66_);
lean_dec(v_example_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim(lean_object* v_motive_68_, uint8_t v_t_69_, lean_object* v_h_70_, lean_object* v_example_71_){
_start:
{
lean_inc(v_example_71_);
return v_example_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___boxed(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_example_75_){
_start:
{
uint8_t v_t_boxed_76_; lean_object* v_res_77_; 
v_t_boxed_76_ = lean_unbox(v_t_73_);
v_res_77_ = l_Lean_Elab_DefKind_example_elim(v_motive_72_, v_t_boxed_76_, v_h_74_, v_example_75_);
lean_dec(v_example_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___redArg(lean_object* v_opaque_78_){
_start:
{
lean_inc(v_opaque_78_);
return v_opaque_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___redArg___boxed(lean_object* v_opaque_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Elab_DefKind_opaque_elim___redArg(v_opaque_79_);
lean_dec(v_opaque_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim(lean_object* v_motive_81_, uint8_t v_t_82_, lean_object* v_h_83_, lean_object* v_opaque_84_){
_start:
{
lean_inc(v_opaque_84_);
return v_opaque_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___boxed(lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_opaque_88_){
_start:
{
uint8_t v_t_boxed_89_; lean_object* v_res_90_; 
v_t_boxed_89_ = lean_unbox(v_t_86_);
v_res_90_ = l_Lean_Elab_DefKind_opaque_elim(v_motive_85_, v_t_boxed_89_, v_h_87_, v_opaque_88_);
lean_dec(v_opaque_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___redArg(lean_object* v_abbrev_91_){
_start:
{
lean_inc(v_abbrev_91_);
return v_abbrev_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___redArg___boxed(lean_object* v_abbrev_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Elab_DefKind_abbrev_elim___redArg(v_abbrev_92_);
lean_dec(v_abbrev_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim(lean_object* v_motive_94_, uint8_t v_t_95_, lean_object* v_h_96_, lean_object* v_abbrev_97_){
_start:
{
lean_inc(v_abbrev_97_);
return v_abbrev_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___boxed(lean_object* v_motive_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_abbrev_101_){
_start:
{
uint8_t v_t_boxed_102_; lean_object* v_res_103_; 
v_t_boxed_102_ = lean_unbox(v_t_99_);
v_res_103_ = l_Lean_Elab_DefKind_abbrev_elim(v_motive_98_, v_t_boxed_102_, v_h_100_, v_abbrev_101_);
lean_dec(v_abbrev_101_);
return v_res_103_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedDefKind_default(void){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedDefKind(void){
_start:
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqDefKind_beq(uint8_t v_x_106_, uint8_t v_y_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_108_ = l_Lean_Elab_DefKind_ctorIdx(v_x_106_);
v___x_109_ = l_Lean_Elab_DefKind_ctorIdx(v_y_107_);
v___x_110_ = lean_nat_dec_eq(v___x_108_, v___x_109_);
lean_dec(v___x_109_);
lean_dec(v___x_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqDefKind_beq___boxed(lean_object* v_x_111_, lean_object* v_y_112_){
_start:
{
uint8_t v_x_17__boxed_113_; uint8_t v_y_18__boxed_114_; uint8_t v_res_115_; lean_object* v_r_116_; 
v_x_17__boxed_113_ = lean_unbox(v_x_111_);
v_y_18__boxed_114_ = lean_unbox(v_y_112_);
v_res_115_ = l_Lean_Elab_instBEqDefKind_beq(v_x_17__boxed_113_, v_y_18__boxed_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t v_x_119_){
_start:
{
if (v_x_119_ == 2)
{
uint8_t v___x_120_; 
v___x_120_ = 1;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isTheorem___boxed(lean_object* v_x_122_){
_start:
{
uint8_t v_x_21__boxed_123_; uint8_t v_res_124_; lean_object* v_r_125_; 
v_x_21__boxed_123_ = lean_unbox(v_x_122_);
v_res_124_ = l_Lean_Elab_DefKind_isTheorem(v_x_21__boxed_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isExample(uint8_t v_x_126_){
_start:
{
if (v_x_126_ == 3)
{
uint8_t v___x_127_; 
v___x_127_ = 1;
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isExample___boxed(lean_object* v_x_129_){
_start:
{
uint8_t v_x_21__boxed_130_; uint8_t v_res_131_; lean_object* v_r_132_; 
v_x_21__boxed_130_ = lean_unbox(v_x_129_);
v_res_131_ = l_Lean_Elab_DefKind_isExample(v_x_21__boxed_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_box(0);
v___x_139_ = ((lean_object*)(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2));
v___x_140_ = l_Lean_Expr_const___override(v___x_139_, v___x_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_141_ = lean_obj_once(&l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3, &l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3_once, _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = ((lean_object*)(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0));
v___x_144_ = lean_box(0);
v___x_145_ = lean_box(0);
v___x_146_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
lean_ctor_set(v___x_146_, 2, v___x_144_);
lean_ctor_set(v___x_146_, 3, v___x_143_);
lean_ctor_set(v___x_146_, 4, v___x_142_);
lean_ctor_set(v___x_146_, 5, v___x_141_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default(void){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4, &l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4_once, _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Elab_instInhabitedDefViewElabHeaderData_default;
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(lean_object* v___f_149_, lean_object* v_x_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_x_150_, v___f_149_, v___y_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed(lean_object* v___f_153_, lean_object* v_x_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(v___f_153_, v_x_154_, v___y_155_);
lean_dec_ref(v___y_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1(lean_object* v___x_157_, lean_object* v___f_158_, lean_object* v_s_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_toSnapshot_161_; lean_object* v_moreSnaps_162_; lean_object* v___x_163_; size_t v_sz_164_; size_t v___x_165_; lean_object* v___x_248__overap_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_toSnapshot_161_ = lean_ctor_get(v_s_159_, 0);
lean_inc_ref(v_toSnapshot_161_);
v_moreSnaps_162_ = lean_ctor_get(v_s_159_, 3);
lean_inc_ref(v_moreSnaps_162_);
lean_dec_ref(v_s_159_);
v___x_163_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_161_, v___y_160_);
v_sz_164_ = lean_array_size(v_moreSnaps_162_);
v___x_165_ = ((size_t)0ULL);
v___x_248__overap_166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_157_, v___f_158_, v_sz_164_, v___x_165_, v_moreSnaps_162_);
lean_inc_ref(v___y_160_);
v___x_167_ = lean_apply_1(v___x_248__overap_166_, v___y_160_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_163_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1___boxed(lean_object* v___x_169_, lean_object* v___f_170_, lean_object* v_s_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1(v___x_169_, v___f_170_, v_s_171_, v___y_172_);
lean_dec_ref(v___y_172_);
return v_res_173_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__9));
v___x_194_ = l_ReaderT_instMonad___redArg(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13(void){
_start:
{
lean_object* v___f_198_; lean_object* v___x_199_; lean_object* v___f_200_; 
v___f_198_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__12));
v___x_199_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10);
v___f_200_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1___boxed), 4, 2);
lean_closure_set(v___f_200_, 0, v___x_199_);
lean_closure_set(v___f_200_, 1, v___f_198_);
return v___f_200_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot(void){
_start:
{
lean_object* v___f_201_; 
v___f_201_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13);
return v___f_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(lean_object* v___x_202_, lean_object* v_x_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_x_203_, v___x_202_, v___y_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(lean_object* v___x_206_, lean_object* v_x_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(v___x_206_, v_x_207_, v___y_208_);
lean_dec_ref(v___y_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2(lean_object* v___x_212_, lean_object* v___f_213_, lean_object* v___f_214_, lean_object* v___f_215_, lean_object* v_s_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_toSnapshot_218_; lean_object* v_tacSnap_x3f_219_; lean_object* v_bodySnap_220_; lean_object* v_moreSnaps_221_; lean_object* v___x_222_; lean_object* v___y_224_; 
v_toSnapshot_218_ = lean_ctor_get(v_s_216_, 0);
lean_inc_ref(v_toSnapshot_218_);
v_tacSnap_x3f_219_ = lean_ctor_get(v_s_216_, 4);
lean_inc(v_tacSnap_x3f_219_);
v_bodySnap_220_ = lean_ctor_get(v_s_216_, 6);
lean_inc_ref(v_bodySnap_220_);
v_moreSnaps_221_ = lean_ctor_get(v_s_216_, 7);
lean_inc_ref(v_moreSnaps_221_);
lean_dec_ref(v_s_216_);
v___x_222_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_218_, v___y_217_);
if (lean_obj_tag(v_tacSnap_x3f_219_) == 0)
{
lean_object* v___x_239_; 
v___x_239_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___closed__0));
v___y_224_ = v___x_239_;
goto v___jp_223_;
}
else
{
lean_object* v_val_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_val_240_ = lean_ctor_get(v_tacSnap_x3f_219_, 0);
lean_inc(v_val_240_);
lean_dec_ref_known(v_tacSnap_x3f_219_, 1);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_mk_empty_array_with_capacity(v___x_241_);
v___x_243_ = lean_array_push(v___x_242_, v_val_240_);
v___y_224_ = v___x_243_;
goto v___jp_223_;
}
v___jp_223_:
{
size_t v_sz_225_; size_t v___x_226_; lean_object* v___x_510__overap_227_; lean_object* v___x_228_; lean_object* v___x_229_; size_t v_sz_230_; lean_object* v___x_512__overap_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_sz_225_ = lean_array_size(v___y_224_);
v___x_226_ = ((size_t)0ULL);
lean_inc_ref(v___x_212_);
v___x_510__overap_227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_212_, v___f_213_, v_sz_225_, v___x_226_, v___y_224_);
lean_inc_ref_n(v___y_217_, 2);
v___x_228_ = lean_apply_1(v___x_510__overap_227_, v___y_217_);
v___x_229_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_bodySnap_220_, v___f_214_, v___y_217_);
v_sz_230_ = lean_array_size(v_moreSnaps_221_);
v___x_512__overap_231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_212_, v___f_215_, v_sz_230_, v___x_226_, v_moreSnaps_221_);
v___x_232_ = lean_apply_1(v___x_512__overap_231_, v___y_217_);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_mk_empty_array_with_capacity(v___x_233_);
v___x_235_ = lean_array_push(v___x_234_, v___x_229_);
v___x_236_ = l_Array_append___redArg(v___x_228_, v___x_235_);
lean_dec_ref(v___x_235_);
v___x_237_ = l_Array_append___redArg(v___x_236_, v___x_232_);
lean_dec_ref(v___x_232_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_222_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___boxed(lean_object* v___x_244_, lean_object* v___f_245_, lean_object* v___f_246_, lean_object* v___f_247_, lean_object* v_s_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2(v___x_244_, v___f_245_, v___f_246_, v___f_247_, v_s_248_, v___y_249_);
lean_dec_ref(v___y_249_);
return v_res_250_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2(void){
_start:
{
lean_object* v___x_254_; lean_object* v___f_255_; 
v___x_254_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot;
v___f_255_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_255_, 0, v___x_254_);
return v___f_255_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3(void){
_start:
{
lean_object* v___f_256_; lean_object* v___f_257_; lean_object* v___f_258_; lean_object* v___x_259_; lean_object* v___f_260_; 
v___f_256_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__12));
v___f_257_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2, &l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2_once, _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2);
v___f_258_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1));
v___x_259_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10);
v___f_260_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___boxed), 6, 4);
lean_closure_set(v___f_260_, 0, v___x_259_);
lean_closure_set(v___f_260_, 1, v___f_258_);
lean_closure_set(v___f_260_, 2, v___f_257_);
lean_closure_set(v___f_260_, 3, v___f_256_);
return v___f_260_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot(void){
_start:
{
lean_object* v___f_261_; 
v___f_261_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3, &l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3_once, _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3);
return v___f_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(lean_object* v___f_271_, lean_object* v_x_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_headerProcessedSnap_274_; lean_object* v___x_275_; 
v_headerProcessedSnap_274_ = lean_ctor_get(v_x_272_, 1);
lean_inc_ref(v_headerProcessedSnap_274_);
lean_dec_ref(v_x_272_);
v___x_275_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_headerProcessedSnap_274_, v___f_271_, v___y_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0___boxed(lean_object* v___f_276_, lean_object* v_x_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(v___f_276_, v_x_277_, v___y_278_);
lean_dec_ref(v___y_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(lean_object* v___x_280_, lean_object* v___f_281_, lean_object* v_s_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_toSnapshot_284_; lean_object* v_defs_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_297_; 
v_toSnapshot_284_ = lean_ctor_get(v_s_282_, 0);
v_defs_285_ = lean_ctor_get(v_s_282_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v_s_282_);
if (v_isSharedCheck_297_ == 0)
{
v___x_287_ = v_s_282_;
v_isShared_288_ = v_isSharedCheck_297_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_defs_285_);
lean_inc(v_toSnapshot_284_);
lean_dec(v_s_282_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_297_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; size_t v_sz_290_; size_t v___x_291_; lean_object* v___x_252__overap_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_289_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_284_, v___y_283_);
v_sz_290_ = lean_array_size(v_defs_285_);
v___x_291_ = ((size_t)0ULL);
v___x_252__overap_292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_280_, v___f_281_, v_sz_290_, v___x_291_, v_defs_285_);
lean_inc_ref(v___y_283_);
v___x_293_ = lean_apply_1(v___x_252__overap_292_, v___y_283_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_293_);
lean_ctor_set(v___x_287_, 0, v___x_289_);
v___x_295_ = v___x_287_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1___boxed(lean_object* v___x_298_, lean_object* v___f_299_, lean_object* v_s_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(v___x_298_, v___f_299_, v_s_300_, v___y_301_);
lean_dec_ref(v___y_301_);
return v_res_302_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0(void){
_start:
{
lean_object* v___x_303_; lean_object* v___f_304_; 
v___x_303_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot;
v___f_304_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_304_, 0, v___x_303_);
return v___f_304_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1(void){
_start:
{
lean_object* v___f_305_; lean_object* v___f_306_; 
v___f_305_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0, &l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_once, _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0);
v___f_306_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0___boxed), 3, 1);
lean_closure_set(v___f_306_, 0, v___f_305_);
return v___f_306_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2(void){
_start:
{
lean_object* v___f_307_; lean_object* v___x_308_; lean_object* v___f_309_; 
v___f_307_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1, &l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_once, _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1);
v___x_308_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10);
v___f_309_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1___boxed), 4, 2);
lean_closure_set(v___f_309_, 0, v___x_308_);
lean_closure_set(v___f_309_, 1, v___f_307_);
return v___f_309_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot(void){
_start:
{
lean_object* v___f_310_; 
v___f_310_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2, &l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_once, _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2);
return v___f_310_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView_default___closed__0(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; lean_object* v___x_315_; 
v___x_311_ = lean_box(0);
v___x_312_ = l_Lean_Elab_instInhabitedModifiers_default;
v___x_313_ = lean_box(0);
v___x_314_ = 0;
v___x_315_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
lean_ctor_set(v___x_315_, 2, v___x_312_);
lean_ctor_set(v___x_315_, 3, v___x_313_);
lean_ctor_set(v___x_315_, 4, v___x_313_);
lean_ctor_set(v___x_315_, 5, v___x_311_);
lean_ctor_set(v___x_315_, 6, v___x_313_);
lean_ctor_set(v___x_315_, 7, v___x_311_);
lean_ctor_set(v___x_315_, 8, v___x_311_);
lean_ctor_set(v___x_315_, 9, v___x_311_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*10, v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView_default(void){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = lean_obj_once(&l_Lean_Elab_instInhabitedDefView_default___closed__0, &l_Lean_Elab_instInhabitedDefView_default___closed__0_once, _init_l_Lean_Elab_instInhabitedDefView_default___closed__0);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Elab_instInhabitedDefView_default;
return v___x_317_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(lean_object* v_as_321_, size_t v_i_322_, size_t v_stop_323_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = lean_usize_dec_eq(v_i_322_, v_stop_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v_name_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_325_ = lean_array_uget_borrowed(v_as_321_, v_i_322_);
v_name_326_ = lean_ctor_get(v___x_325_, 0);
v___x_327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1));
v___x_328_ = lean_name_eq(v_name_326_, v___x_327_);
if (v___x_328_ == 0)
{
size_t v___x_329_; size_t v___x_330_; 
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_add(v_i_322_, v___x_329_);
v_i_322_ = v___x_330_;
goto _start;
}
else
{
return v___x_328_;
}
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___boxed(lean_object* v_as_333_, lean_object* v_i_334_, lean_object* v_stop_335_){
_start:
{
size_t v_i_boxed_336_; size_t v_stop_boxed_337_; uint8_t v_res_338_; lean_object* v_r_339_; 
v_i_boxed_336_ = lean_unbox_usize(v_i_334_);
lean_dec(v_i_334_);
v_stop_boxed_337_ = lean_unbox_usize(v_stop_335_);
lean_dec(v_stop_335_);
v_res_338_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_as_333_, v_i_boxed_336_, v_stop_boxed_337_);
lean_dec_ref(v_as_333_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_isInstance(lean_object* v_view_340_){
_start:
{
lean_object* v_modifiers_341_; lean_object* v_attrs_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_modifiers_341_ = lean_ctor_get(v_view_340_, 2);
v_attrs_342_ = lean_ctor_get(v_modifiers_341_, 2);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_array_get_size(v_attrs_342_);
v___x_345_ = lean_nat_dec_lt(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
return v___x_345_;
}
else
{
if (v___x_345_ == 0)
{
return v___x_345_;
}
else
{
size_t v___x_346_; size_t v___x_347_; uint8_t v___x_348_; 
v___x_346_ = ((size_t)0ULL);
v___x_347_ = lean_usize_of_nat(v___x_344_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_attrs_342_, v___x_346_, v___x_347_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_isInstance___boxed(lean_object* v_view_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_Lean_Elab_DefView_isInstance(v_view_349_);
lean_dec_ref(v_view_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_markDefEq___lam__0(lean_object* v_x_355_){
_start:
{
lean_object* v_name_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v_name_356_ = lean_ctor_get(v_x_355_, 0);
v___x_357_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___lam__0___closed__1));
v___x_358_ = lean_name_eq(v_name_356_, v___x_357_);
if (v___x_358_ == 0)
{
uint8_t v___x_359_; 
v___x_359_ = 1;
return v___x_359_;
}
else
{
uint8_t v___x_360_; 
v___x_360_ = 0;
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_markDefEq___lam__0___boxed(lean_object* v_x_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Lean_Elab_DefView_markDefEq___lam__0(v_x_361_);
lean_dec_ref(v_x_361_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_markDefEq(lean_object* v_view_369_){
_start:
{
uint8_t v_kind_370_; lean_object* v_ref_371_; lean_object* v_headerRef_372_; lean_object* v_modifiers_373_; lean_object* v_declId_374_; lean_object* v_binders_375_; lean_object* v_type_x3f_376_; lean_object* v_value_377_; lean_object* v_docString_x3f_378_; lean_object* v_headerSnap_x3f_379_; lean_object* v_deriving_x3f_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_391_; 
v_kind_370_ = lean_ctor_get_uint8(v_view_369_, sizeof(void*)*10);
v_ref_371_ = lean_ctor_get(v_view_369_, 0);
v_headerRef_372_ = lean_ctor_get(v_view_369_, 1);
v_modifiers_373_ = lean_ctor_get(v_view_369_, 2);
v_declId_374_ = lean_ctor_get(v_view_369_, 3);
v_binders_375_ = lean_ctor_get(v_view_369_, 4);
v_type_x3f_376_ = lean_ctor_get(v_view_369_, 5);
v_value_377_ = lean_ctor_get(v_view_369_, 6);
v_docString_x3f_378_ = lean_ctor_get(v_view_369_, 7);
v_headerSnap_x3f_379_ = lean_ctor_get(v_view_369_, 8);
v_deriving_x3f_380_ = lean_ctor_get(v_view_369_, 9);
v_isSharedCheck_391_ = !lean_is_exclusive(v_view_369_);
if (v_isSharedCheck_391_ == 0)
{
v___x_382_ = v_view_369_;
v_isShared_383_ = v_isSharedCheck_391_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_deriving_x3f_380_);
lean_inc(v_headerSnap_x3f_379_);
lean_inc(v_docString_x3f_378_);
lean_inc(v_value_377_);
lean_inc(v_type_x3f_376_);
lean_inc(v_binders_375_);
lean_inc(v_declId_374_);
lean_inc(v_modifiers_373_);
lean_inc(v_headerRef_372_);
lean_inc(v_ref_371_);
lean_dec(v_view_369_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_391_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___f_384_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___closed__0));
v___x_385_ = l_Lean_Elab_Modifiers_filterAttrs(v_modifiers_373_, v___f_384_);
v___x_386_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___closed__1));
v___x_387_ = l_Lean_Elab_Modifiers_addFirstAttr(v___x_385_, v___x_386_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 2, v___x_387_);
v___x_389_ = v___x_382_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_ref_371_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_headerRef_372_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_declId_374_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v_binders_375_);
lean_ctor_set(v_reuseFailAlloc_390_, 5, v_type_x3f_376_);
lean_ctor_set(v_reuseFailAlloc_390_, 6, v_value_377_);
lean_ctor_set(v_reuseFailAlloc_390_, 7, v_docString_x3f_378_);
lean_ctor_set(v_reuseFailAlloc_390_, 8, v_headerSnap_x3f_379_);
lean_ctor_set(v_reuseFailAlloc_390_, 9, v_deriving_x3f_380_);
lean_ctor_set_uint8(v_reuseFailAlloc_390_, sizeof(void*)*10, v_kind_370_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev(lean_object* v_modifiers_409_, lean_object* v_stx_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_416_; lean_object* v_modifiers_417_; lean_object* v___x_418_; lean_object* v_modifiers_419_; lean_object* v_docString_x3f_420_; uint8_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_411_ = lean_unsigned_to_nat(2u);
v___x_412_ = l_Lean_Syntax_getArg(v_stx_410_, v___x_411_);
v___x_413_ = l_Lean_Elab_expandOptDeclSig(v___x_412_);
lean_dec(v___x_412_);
v_fst_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_fst_414_);
v_snd_415_ = lean_ctor_get(v___x_413_, 1);
lean_inc(v_snd_415_);
lean_dec_ref(v___x_413_);
v___x_416_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2));
v_modifiers_417_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_409_, v___x_416_);
v___x_418_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5));
v_modifiers_419_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_417_, v___x_418_);
v_docString_x3f_420_ = lean_ctor_get(v_modifiers_419_, 1);
lean_inc(v_docString_x3f_420_);
v___x_421_ = 5;
v___x_422_ = l_Lean_Syntax_getArgs(v_stx_410_);
v___x_423_ = lean_unsigned_to_nat(3u);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = l_Array_toSubarray___redArg(v___x_422_, v___x_424_, v___x_423_);
v___x_426_ = l_Subarray_copy___redArg(v___x_425_);
v___x_427_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_428_ = lean_box(2);
v___x_429_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
lean_ctor_set(v___x_429_, 2, v___x_426_);
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = l_Lean_Syntax_getArg(v_stx_410_, v___x_430_);
v___x_432_ = l_Lean_Syntax_getArg(v_stx_410_, v___x_423_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_434_, 0, v_stx_410_);
lean_ctor_set(v___x_434_, 1, v___x_429_);
lean_ctor_set(v___x_434_, 2, v_modifiers_419_);
lean_ctor_set(v___x_434_, 3, v___x_431_);
lean_ctor_set(v___x_434_, 4, v_fst_414_);
lean_ctor_set(v___x_434_, 5, v_snd_415_);
lean_ctor_set(v___x_434_, 6, v___x_432_);
lean_ctor_set(v___x_434_, 7, v_docString_x3f_420_);
lean_ctor_set(v___x_434_, 8, v___x_433_);
lean_ctor_set(v___x_434_, 9, v___x_433_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*10, v___x_421_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfDef(lean_object* v_modifiers_435_, lean_object* v_stx_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v_fst_440_; lean_object* v_snd_441_; lean_object* v___y_443_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_437_ = lean_unsigned_to_nat(2u);
v___x_438_ = l_Lean_Syntax_getArg(v_stx_436_, v___x_437_);
v___x_439_ = l_Lean_Elab_expandOptDeclSig(v___x_438_);
lean_dec(v___x_438_);
v_fst_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_fst_440_);
v_snd_441_ = lean_ctor_get(v___x_439_, 1);
lean_inc(v_snd_441_);
lean_dec_ref(v___x_439_);
v___x_459_ = lean_unsigned_to_nat(4u);
v___x_460_ = l_Lean_Syntax_getArg(v_stx_436_, v___x_459_);
v___x_461_ = l_Lean_Syntax_isNone(v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = lean_unsigned_to_nat(1u);
v___x_463_ = l_Lean_Syntax_getArg(v___x_460_, v___x_462_);
lean_dec(v___x_460_);
v___x_464_ = l_Lean_Syntax_getSepArgs(v___x_463_);
lean_dec(v___x_463_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
v___y_443_ = v___x_465_;
goto v___jp_442_;
}
else
{
lean_object* v___x_466_; 
lean_dec(v___x_460_);
v___x_466_ = lean_box(0);
v___y_443_ = v___x_466_;
goto v___jp_442_;
}
v___jp_442_:
{
lean_object* v_docString_x3f_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_docString_x3f_444_ = lean_ctor_get(v_modifiers_435_, 1);
lean_inc(v_docString_x3f_444_);
v___x_445_ = 0;
v___x_446_ = l_Lean_Syntax_getArgs(v_stx_436_);
v___x_447_ = lean_unsigned_to_nat(3u);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = l_Array_toSubarray___redArg(v___x_446_, v___x_448_, v___x_447_);
v___x_450_ = l_Subarray_copy___redArg(v___x_449_);
v___x_451_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_452_ = lean_box(2);
v___x_453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_450_);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = l_Lean_Syntax_getArg(v_stx_436_, v___x_454_);
v___x_456_ = l_Lean_Syntax_getArg(v_stx_436_, v___x_447_);
v___x_457_ = lean_box(0);
v___x_458_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_458_, 0, v_stx_436_);
lean_ctor_set(v___x_458_, 1, v___x_453_);
lean_ctor_set(v___x_458_, 2, v_modifiers_435_);
lean_ctor_set(v___x_458_, 3, v___x_455_);
lean_ctor_set(v___x_458_, 4, v_fst_440_);
lean_ctor_set(v___x_458_, 5, v_snd_441_);
lean_ctor_set(v___x_458_, 6, v___x_456_);
lean_ctor_set(v___x_458_, 7, v_docString_x3f_444_);
lean_ctor_set(v___x_458_, 8, v___x_457_);
lean_ctor_set(v___x_458_, 9, v___y_443_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*10, v___x_445_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem(lean_object* v_modifiers_467_, lean_object* v_stx_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v_docString_x3f_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_469_ = lean_unsigned_to_nat(2u);
v___x_470_ = l_Lean_Syntax_getArg(v_stx_468_, v___x_469_);
v___x_471_ = l_Lean_Elab_expandDeclSig(v___x_470_);
lean_dec(v___x_470_);
v_fst_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_fst_472_);
v_snd_473_ = lean_ctor_get(v___x_471_, 1);
lean_inc(v_snd_473_);
lean_dec_ref(v___x_471_);
v_docString_x3f_474_ = lean_ctor_get(v_modifiers_467_, 1);
lean_inc(v_docString_x3f_474_);
v___x_475_ = 2;
v___x_476_ = l_Lean_Syntax_getArgs(v_stx_468_);
v___x_477_ = lean_unsigned_to_nat(3u);
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = l_Array_toSubarray___redArg(v___x_476_, v___x_478_, v___x_477_);
v___x_480_ = l_Subarray_copy___redArg(v___x_479_);
v___x_481_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_482_ = lean_box(2);
v___x_483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
lean_ctor_set(v___x_483_, 2, v___x_480_);
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = l_Lean_Syntax_getArg(v_stx_468_, v___x_484_);
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v_snd_473_);
v___x_487_ = l_Lean_Syntax_getArg(v_stx_468_, v___x_477_);
v___x_488_ = lean_box(0);
v___x_489_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_489_, 0, v_stx_468_);
lean_ctor_set(v___x_489_, 1, v___x_483_);
lean_ctor_set(v___x_489_, 2, v_modifiers_467_);
lean_ctor_set(v___x_489_, 3, v___x_485_);
lean_ctor_set(v___x_489_, 4, v_fst_472_);
lean_ctor_set(v___x_489_, 5, v___x_486_);
lean_ctor_set(v___x_489_, 6, v___x_487_);
lean_ctor_set(v___x_489_, 7, v_docString_x3f_474_);
lean_ctor_set(v___x_489_, 8, v___x_488_);
lean_ctor_set(v___x_489_, 9, v___x_488_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*10, v___x_475_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; lean_object* v_env_493_; lean_object* v___x_494_; lean_object* v_mainModule_495_; lean_object* v___x_496_; 
v___x_492_ = lean_st_ref_get(v___y_490_);
v_env_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc_ref(v_env_493_);
lean_dec(v___x_492_);
v___x_494_ = l_Lean_Environment_header(v_env_493_);
lean_dec_ref(v_env_493_);
v_mainModule_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_mainModule_495_);
lean_dec_ref(v___x_494_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v_mainModule_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg___boxed(lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_497_);
lean_dec(v___y_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___boxed(lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_507_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = l_Lean_maxRecDepthErrorMessage;
v___x_514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3);
v___x_516_ = l_Lean_MessageData_ofFormat(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4);
v___x_518_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2));
v___x_519_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v___x_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(lean_object* v_ref_520_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_ref_520_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___boxed(lean_object* v_ref_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(lean_object* v_x_528_, lean_object* v___y_529_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_531_; 
v_a_530_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_a_530_);
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v_a_530_);
lean_ctor_set(v___x_531_, 1, v___y_529_);
return v___x_531_;
}
else
{
lean_object* v_a_532_; lean_object* v___x_533_; 
v_a_532_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_a_532_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v_a_532_);
lean_ctor_set(v___x_533_, 1, v___y_529_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg___boxed(lean_object* v_x_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_534_, v___y_535_);
lean_dec_ref(v_x_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(lean_object* v_env_537_, lean_object* v_stx_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_537_, v_stx_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
if (lean_obj_tag(v_a_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
v_a_543_ = lean_ctor_get(v___x_541_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v___x_541_, 0);
lean_dec(v_unused_552_);
v___x_545_ = v___x_541_;
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_541_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_box(0);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_a_543_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v_val_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_581_; 
v_val_553_ = lean_ctor_get(v_a_542_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v_a_542_);
if (v_isSharedCheck_581_ == 0)
{
v___x_555_ = v_a_542_;
v_isShared_556_ = v_isSharedCheck_581_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_val_553_);
lean_dec(v_a_542_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_581_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v_snd_557_; 
v_snd_557_ = lean_ctor_get(v_val_553_, 1);
lean_inc(v_snd_557_);
lean_dec(v_val_553_);
if (lean_obj_tag(v_snd_557_) == 0)
{
lean_object* v_a_558_; lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
lean_del_object(v___x_555_);
v_a_558_ = lean_ctor_get(v___x_541_, 1);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_541_, 2);
v_a_559_ = lean_ctor_get(v_snd_557_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v_snd_557_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v_snd_557_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v_snd_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_566_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; 
v___x_565_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_564_, v_a_558_);
lean_dec_ref(v___x_564_);
return v___x_565_;
}
}
}
else
{
lean_object* v_a_568_; lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_580_; 
v_a_568_ = lean_ctor_get(v___x_541_, 1);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_541_, 2);
v_a_569_ = lean_ctor_get(v_snd_557_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v_snd_557_);
if (v_isSharedCheck_580_ == 0)
{
v___x_571_ = v_snd_557_;
v_isShared_572_ = v_isSharedCheck_580_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v_snd_557_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_580_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v_a_569_);
v___x_574_ = v___x_555_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_579_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_574_);
v___x_576_ = v___x_571_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_578_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; 
v___x_577_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_576_, v_a_568_);
lean_dec_ref(v___x_576_);
return v___x_577_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_a_582_ = lean_ctor_get(v___x_541_, 0);
v_a_583_ = lean_ctor_get(v___x_541_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_541_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_inc(v_a_582_);
lean_dec(v___x_541_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_582_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed(lean_object* v_env_591_, lean_object* v_stx_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(v_env_591_, v_stx_592_, v___y_593_, v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(lean_object* v_currNamespace_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_currNamespace_596_);
lean_ctor_set(v___x_599_, 1, v___y_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(v_currNamespace_600_, v___y_601_, v___y_602_);
lean_dec_ref(v___y_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(lean_object* v_env_604_, lean_object* v_currNamespace_605_, lean_object* v_openDecls_606_, lean_object* v_n_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = l_Lean_ResolveName_resolveNamespace(v_env_604_, v_currNamespace_605_, v_openDecls_606_, v_n_607_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___y_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed(lean_object* v_env_612_, lean_object* v_currNamespace_613_, lean_object* v_openDecls_614_, lean_object* v_n_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(v_env_612_, v_currNamespace_613_, v_openDecls_614_, v_n_615_, v___y_616_, v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(lean_object* v_env_619_, lean_object* v_declName_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_623_; lean_object* v_env_624_; lean_object* v___x_625_; uint8_t v___x_626_; uint8_t v___x_627_; 
v___x_623_ = 0;
v_env_624_ = l_Lean_Environment_setExporting(v_env_619_, v___x_623_);
lean_inc(v_declName_620_);
v___x_625_ = l_Lean_mkPrivateName(v_env_624_, v_declName_620_);
v___x_626_ = 1;
lean_inc_ref(v_env_624_);
v___x_627_ = l_Lean_Environment_contains(v_env_624_, v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = l_Lean_privateToUserName(v_declName_620_);
v___x_629_ = l_Lean_Environment_contains(v_env_624_, v___x_628_, v___x_626_);
v___x_630_ = lean_box(v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___y_622_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref(v_env_624_);
lean_dec(v_declName_620_);
v___x_632_ = lean_box(v___x_627_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___y_622_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed(lean_object* v_env_634_, lean_object* v_declName_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(v_env_634_, v_declName_635_, v___y_636_, v___y_637_);
lean_dec_ref(v___y_636_);
return v_res_638_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_639_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
lean_ctor_set(v___x_644_, 2, v___x_643_);
lean_ctor_set(v___x_644_, 3, v___x_643_);
lean_ctor_set(v___x_644_, 4, v___x_642_);
lean_ctor_set(v___x_644_, 5, v___x_642_);
lean_ctor_set(v___x_644_, 6, v___x_642_);
lean_ctor_set(v___x_644_, 7, v___x_642_);
lean_ctor_set(v___x_644_, 8, v___x_642_);
lean_ctor_set(v___x_644_, 9, v___x_642_);
lean_ctor_set(v___x_644_, 10, v___x_642_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_unsigned_to_nat(32u);
v___x_646_ = lean_mk_empty_array_with_capacity(v___x_645_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_648_ = ((size_t)5ULL);
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_unsigned_to_nat(32u);
v___x_651_ = lean_mk_empty_array_with_capacity(v___x_650_);
v___x_652_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3);
v___x_653_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
lean_ctor_set(v___x_653_, 2, v___x_649_);
lean_ctor_set(v___x_653_, 3, v___x_649_);
lean_ctor_set_usize(v___x_653_, 4, v___x_648_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = lean_box(1);
v___x_655_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4);
v___x_656_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
v___x_657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
lean_ctor_set(v___x_657_, 2, v___x_654_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(lean_object* v_msgData_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; lean_object* v_env_662_; lean_object* v___x_663_; lean_object* v_scopes_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v_opts_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_661_ = lean_st_ref_get(v___y_659_);
v_env_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc_ref(v_env_662_);
lean_dec(v___x_661_);
v___x_663_ = lean_st_ref_get(v___y_659_);
v_scopes_664_ = lean_ctor_get(v___x_663_, 2);
lean_inc(v_scopes_664_);
lean_dec(v___x_663_);
v___x_665_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_666_ = l_List_head_x21___redArg(v___x_665_, v_scopes_664_);
lean_dec(v_scopes_664_);
v_opts_667_ = lean_ctor_get(v___x_666_, 1);
lean_inc_ref(v_opts_667_);
lean_dec(v___x_666_);
v___x_668_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2);
v___x_669_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5);
v___x_670_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_670_, 0, v_env_662_);
lean_ctor_set(v___x_670_, 1, v___x_668_);
lean_ctor_set(v___x_670_, 2, v___x_669_);
lean_ctor_set(v___x_670_, 3, v_opts_667_);
v___x_671_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v_msgData_658_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___boxed(lean_object* v_msgData_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_673_, v___y_674_);
lean_dec(v___y_674_);
return v_res_676_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0(void){
_start:
{
lean_object* v___x_677_; double v___x_678_; 
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_float_of_nat(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(lean_object* v_cls_682_, lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Elab_Command_getRef___redArg(v___y_684_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_689_; lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_737_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_683_, v___y_685_);
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_737_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_737_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_737_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v_traceState_695_; lean_object* v_env_696_; lean_object* v_messages_697_; lean_object* v_scopes_698_; lean_object* v_usedQuotCtxts_699_; lean_object* v_nextMacroScope_700_; lean_object* v_maxRecDepth_701_; lean_object* v_ngen_702_; lean_object* v_auxDeclNGen_703_; lean_object* v_infoState_704_; lean_object* v_snapshotTasks_705_; lean_object* v_prevLinterStates_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_736_; 
v___x_694_ = lean_st_ref_take(v___y_685_);
v_traceState_695_ = lean_ctor_get(v___x_694_, 9);
v_env_696_ = lean_ctor_get(v___x_694_, 0);
v_messages_697_ = lean_ctor_get(v___x_694_, 1);
v_scopes_698_ = lean_ctor_get(v___x_694_, 2);
v_usedQuotCtxts_699_ = lean_ctor_get(v___x_694_, 3);
v_nextMacroScope_700_ = lean_ctor_get(v___x_694_, 4);
v_maxRecDepth_701_ = lean_ctor_get(v___x_694_, 5);
v_ngen_702_ = lean_ctor_get(v___x_694_, 6);
v_auxDeclNGen_703_ = lean_ctor_get(v___x_694_, 7);
v_infoState_704_ = lean_ctor_get(v___x_694_, 8);
v_snapshotTasks_705_ = lean_ctor_get(v___x_694_, 10);
v_prevLinterStates_706_ = lean_ctor_get(v___x_694_, 11);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_736_ == 0)
{
v___x_708_ = v___x_694_;
v_isShared_709_ = v_isSharedCheck_736_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_prevLinterStates_706_);
lean_inc(v_snapshotTasks_705_);
lean_inc(v_traceState_695_);
lean_inc(v_infoState_704_);
lean_inc(v_auxDeclNGen_703_);
lean_inc(v_ngen_702_);
lean_inc(v_maxRecDepth_701_);
lean_inc(v_nextMacroScope_700_);
lean_inc(v_usedQuotCtxts_699_);
lean_inc(v_scopes_698_);
lean_inc(v_messages_697_);
lean_inc(v_env_696_);
lean_dec(v___x_694_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_736_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
uint64_t v_tid_710_; lean_object* v_traces_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_735_; 
v_tid_710_ = lean_ctor_get_uint64(v_traceState_695_, sizeof(void*)*1);
v_traces_711_ = lean_ctor_get(v_traceState_695_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v_traceState_695_);
if (v_isSharedCheck_735_ == 0)
{
v___x_713_ = v_traceState_695_;
v_isShared_714_ = v_isSharedCheck_735_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_traces_711_);
lean_dec(v_traceState_695_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_735_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; double v___x_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_715_ = lean_box(0);
v___x_716_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0);
v___x_717_ = 0;
v___x_718_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1));
v___x_719_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_719_, 0, v_cls_682_);
lean_ctor_set(v___x_719_, 1, v___x_715_);
lean_ctor_set(v___x_719_, 2, v___x_718_);
lean_ctor_set_float(v___x_719_, sizeof(void*)*3, v___x_716_);
lean_ctor_set_float(v___x_719_, sizeof(void*)*3 + 8, v___x_716_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*3 + 16, v___x_717_);
v___x_720_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2));
v___x_721_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v_a_690_);
lean_ctor_set(v___x_721_, 2, v___x_720_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_a_688_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = l_Lean_PersistentArray_push___redArg(v_traces_711_, v___x_722_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_723_);
v___x_725_ = v___x_713_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_723_);
lean_ctor_set_uint64(v_reuseFailAlloc_734_, sizeof(void*)*1, v_tid_710_);
v___x_725_ = v_reuseFailAlloc_734_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 9, v___x_725_);
v___x_727_ = v___x_708_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_env_696_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_messages_697_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_scopes_698_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_usedQuotCtxts_699_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_nextMacroScope_700_);
lean_ctor_set(v_reuseFailAlloc_733_, 5, v_maxRecDepth_701_);
lean_ctor_set(v_reuseFailAlloc_733_, 6, v_ngen_702_);
lean_ctor_set(v_reuseFailAlloc_733_, 7, v_auxDeclNGen_703_);
lean_ctor_set(v_reuseFailAlloc_733_, 8, v_infoState_704_);
lean_ctor_set(v_reuseFailAlloc_733_, 9, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_733_, 10, v_snapshotTasks_705_);
lean_ctor_set(v_reuseFailAlloc_733_, 11, v_prevLinterStates_706_);
v___x_727_ = v_reuseFailAlloc_733_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_728_ = lean_st_ref_put(v___y_685_, v___x_727_);
v___x_729_ = lean_box(0);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_729_);
v___x_731_ = v___x_692_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v_msg_683_);
lean_dec(v_cls_682_);
v_a_738_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_687_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_687_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___boxed(lean_object* v_cls_746_, lean_object* v_msg_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_cls_746_, v_msg_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_751_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(lean_object* v_keys_752_, lean_object* v_i_753_, lean_object* v_k_754_){
_start:
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = lean_array_get_size(v_keys_752_);
v___x_756_ = lean_nat_dec_lt(v_i_753_, v___x_755_);
if (v___x_756_ == 0)
{
lean_dec(v_i_753_);
return v___x_756_;
}
else
{
lean_object* v_k_x27_757_; uint8_t v___x_758_; 
v_k_x27_757_ = lean_array_fget_borrowed(v_keys_752_, v_i_753_);
v___x_758_ = l_Lean_instBEqExtraModUse_beq(v_k_754_, v_k_x27_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_nat_add(v_i_753_, v___x_759_);
lean_dec(v_i_753_);
v_i_753_ = v___x_760_;
goto _start;
}
else
{
lean_dec(v_i_753_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg___boxed(lean_object* v_keys_762_, lean_object* v_i_763_, lean_object* v_k_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_762_, v_i_763_, v_k_764_);
lean_dec_ref(v_k_764_);
lean_dec_ref(v_keys_762_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(lean_object* v_x_767_, size_t v_x_768_, lean_object* v_x_769_){
_start:
{
if (lean_obj_tag(v_x_767_) == 0)
{
lean_object* v_es_770_; lean_object* v___x_771_; size_t v___x_772_; size_t v___x_773_; lean_object* v_j_774_; lean_object* v___x_775_; 
v_es_770_ = lean_ctor_get(v_x_767_, 0);
v___x_771_ = lean_box(2);
v___x_772_ = ((size_t)31ULL);
v___x_773_ = lean_usize_land(v_x_768_, v___x_772_);
v_j_774_ = lean_usize_to_nat(v___x_773_);
v___x_775_ = lean_array_get_borrowed(v___x_771_, v_es_770_, v_j_774_);
lean_dec(v_j_774_);
switch(lean_obj_tag(v___x_775_))
{
case 0:
{
lean_object* v_key_776_; uint8_t v___x_777_; 
v_key_776_ = lean_ctor_get(v___x_775_, 0);
v___x_777_ = l_Lean_instBEqExtraModUse_beq(v_x_769_, v_key_776_);
return v___x_777_;
}
case 1:
{
lean_object* v_node_778_; size_t v___x_779_; size_t v___x_780_; 
v_node_778_ = lean_ctor_get(v___x_775_, 0);
v___x_779_ = ((size_t)5ULL);
v___x_780_ = lean_usize_shift_right(v_x_768_, v___x_779_);
v_x_767_ = v_node_778_;
v_x_768_ = v___x_780_;
goto _start;
}
default: 
{
uint8_t v___x_782_; 
v___x_782_ = 0;
return v___x_782_;
}
}
}
else
{
lean_object* v_ks_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_ks_783_ = lean_ctor_get(v_x_767_, 0);
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_ks_783_, v___x_784_, v_x_769_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
size_t v_x_17233__boxed_789_; uint8_t v_res_790_; lean_object* v_r_791_; 
v_x_17233__boxed_789_ = lean_unbox_usize(v_x_787_);
lean_dec(v_x_787_);
v_res_790_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_786_, v_x_17233__boxed_789_, v_x_788_);
lean_dec_ref(v_x_788_);
lean_dec_ref(v_x_786_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
uint64_t v___x_794_; size_t v___x_795_; uint8_t v___x_796_; 
v___x_794_ = l_Lean_instHashableExtraModUse_hash(v_x_793_);
v___x_795_ = lean_uint64_to_usize(v___x_794_);
v___x_796_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_792_, v___x_795_, v_x_793_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_797_, v_x_798_);
lean_dec_ref(v_x_798_);
lean_dec_ref(v_x_797_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1));
v___x_804_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0));
v___x_805_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_804_, v___x_803_);
return v___x_805_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5));
v___x_811_ = l_Lean_stringToMessageData(v___x_810_);
return v___x_811_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7));
v___x_814_ = l_Lean_stringToMessageData(v___x_813_);
return v___x_814_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1));
v___x_816_ = l_Lean_stringToMessageData(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_cls_820_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4));
v___x_821_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11));
v___x_822_ = l_Lean_Name_append(v___x_821_, v_cls_820_);
return v___x_822_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(lean_object* v_mod_833_, uint8_t v_isMeta_834_, lean_object* v_hint_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; lean_object* v_env_840_; uint8_t v_isExporting_841_; lean_object* v___x_842_; lean_object* v_env_843_; lean_object* v___x_844_; lean_object* v_entry_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___y_850_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_839_ = lean_st_ref_get(v___y_837_);
v_env_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc_ref(v_env_840_);
lean_dec(v___x_839_);
v_isExporting_841_ = lean_ctor_get_uint8(v_env_840_, sizeof(void*)*8);
lean_dec_ref(v_env_840_);
v___x_842_ = lean_st_ref_get(v___y_837_);
v_env_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_env_843_);
lean_dec(v___x_842_);
v___x_844_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2);
lean_inc(v_mod_833_);
v_entry_845_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_845_, 0, v_mod_833_);
lean_ctor_set_uint8(v_entry_845_, sizeof(void*)*1, v_isExporting_841_);
lean_ctor_set_uint8(v_entry_845_, sizeof(void*)*1 + 1, v_isMeta_834_);
v___x_846_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_847_ = lean_box(1);
v___x_848_ = lean_box(0);
v___x_877_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_844_, v___x_846_, v_env_843_, v___x_847_, v___x_848_);
v___x_878_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v___x_877_, v_entry_845_);
lean_dec(v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_scopes_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_opts_885_; uint8_t v_hasTrace_886_; 
v___x_879_ = l_Lean_inheritedTraceOptions;
v___x_880_ = lean_st_ref_get(v___x_879_);
v___x_881_ = lean_st_ref_get(v___y_837_);
v_scopes_882_ = lean_ctor_get(v___x_881_, 2);
lean_inc(v_scopes_882_);
lean_dec(v___x_881_);
v___x_883_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_884_ = l_List_head_x21___redArg(v___x_883_, v_scopes_882_);
lean_dec(v_scopes_882_);
v_opts_885_ = lean_ctor_get(v___x_884_, 1);
lean_inc_ref(v_opts_885_);
lean_dec(v___x_884_);
v_hasTrace_886_ = lean_ctor_get_uint8(v_opts_885_, sizeof(void*)*1);
if (v_hasTrace_886_ == 0)
{
lean_dec_ref(v_opts_885_);
lean_dec(v___x_880_);
lean_dec(v_hint_835_);
lean_dec(v_mod_833_);
v___y_850_ = v___y_837_;
goto v___jp_849_;
}
else
{
lean_object* v_cls_887_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_cls_887_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4));
v___x_907_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12);
v___x_908_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_880_, v_opts_885_, v___x_907_);
lean_dec_ref(v_opts_885_);
lean_dec(v___x_880_);
if (v___x_908_ == 0)
{
lean_dec(v_hint_835_);
lean_dec(v_mod_833_);
v___y_850_ = v___y_837_;
goto v___jp_849_;
}
else
{
lean_object* v___x_909_; lean_object* v___y_911_; 
v___x_909_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14);
if (v_isExporting_841_ == 0)
{
lean_object* v___x_918_; 
v___x_918_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19));
v___y_911_ = v___x_918_;
goto v___jp_910_;
}
else
{
lean_object* v___x_919_; 
v___x_919_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20));
v___y_911_ = v___x_919_;
goto v___jp_910_;
}
v___jp_910_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_inc_ref(v___y_911_);
v___x_912_ = l_Lean_stringToMessageData(v___y_911_);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_909_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
if (v_isMeta_834_ == 0)
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17));
v___y_894_ = v___x_915_;
v___y_895_ = v___x_916_;
goto v___jp_893_;
}
else
{
lean_object* v___x_917_; 
v___x_917_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18));
v___y_894_ = v___x_915_;
v___y_895_ = v___x_917_;
goto v___jp_893_;
}
}
}
v___jp_888_:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___y_889_);
lean_ctor_set(v___x_891_, 1, v___y_890_);
v___x_892_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_cls_887_, v___x_891_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_dec_ref_known(v___x_892_, 1);
v___y_850_ = v___y_837_;
goto v___jp_849_;
}
else
{
lean_dec_ref_known(v_entry_845_, 1);
return v___x_892_;
}
}
v___jp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
lean_inc_ref(v___y_895_);
v___x_896_ = l_Lean_stringToMessageData(v___y_895_);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v___y_894_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = l_Lean_MessageData_ofName(v_mod_833_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Lean_Name_isAnonymous(v_hint_835_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8);
v___x_904_ = l_Lean_MessageData_ofName(v_hint_835_);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___y_889_ = v___x_901_;
v___y_890_ = v___x_905_;
goto v___jp_888_;
}
else
{
lean_object* v___x_906_; 
lean_dec(v_hint_835_);
v___x_906_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9);
v___y_889_ = v___x_901_;
v___y_890_ = v___x_906_;
goto v___jp_888_;
}
}
}
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; 
lean_dec_ref_known(v_entry_845_, 1);
lean_dec(v_hint_835_);
lean_dec(v_mod_833_);
v___x_920_ = lean_box(0);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
v___jp_849_:
{
lean_object* v___x_851_; lean_object* v_toEnvExtension_852_; lean_object* v_env_853_; lean_object* v_messages_854_; lean_object* v_scopes_855_; lean_object* v_usedQuotCtxts_856_; lean_object* v_nextMacroScope_857_; lean_object* v_maxRecDepth_858_; lean_object* v_ngen_859_; lean_object* v_auxDeclNGen_860_; lean_object* v_infoState_861_; lean_object* v_traceState_862_; lean_object* v_snapshotTasks_863_; lean_object* v_prevLinterStates_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_876_; 
v___x_851_ = lean_st_ref_take(v___y_850_);
v_toEnvExtension_852_ = lean_ctor_get(v___x_846_, 0);
v_env_853_ = lean_ctor_get(v___x_851_, 0);
v_messages_854_ = lean_ctor_get(v___x_851_, 1);
v_scopes_855_ = lean_ctor_get(v___x_851_, 2);
v_usedQuotCtxts_856_ = lean_ctor_get(v___x_851_, 3);
v_nextMacroScope_857_ = lean_ctor_get(v___x_851_, 4);
v_maxRecDepth_858_ = lean_ctor_get(v___x_851_, 5);
v_ngen_859_ = lean_ctor_get(v___x_851_, 6);
v_auxDeclNGen_860_ = lean_ctor_get(v___x_851_, 7);
v_infoState_861_ = lean_ctor_get(v___x_851_, 8);
v_traceState_862_ = lean_ctor_get(v___x_851_, 9);
v_snapshotTasks_863_ = lean_ctor_get(v___x_851_, 10);
v_prevLinterStates_864_ = lean_ctor_get(v___x_851_, 11);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_876_ == 0)
{
v___x_866_ = v___x_851_;
v_isShared_867_ = v_isSharedCheck_876_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_prevLinterStates_864_);
lean_inc(v_snapshotTasks_863_);
lean_inc(v_traceState_862_);
lean_inc(v_infoState_861_);
lean_inc(v_auxDeclNGen_860_);
lean_inc(v_ngen_859_);
lean_inc(v_maxRecDepth_858_);
lean_inc(v_nextMacroScope_857_);
lean_inc(v_usedQuotCtxts_856_);
lean_inc(v_scopes_855_);
lean_inc(v_messages_854_);
lean_inc(v_env_853_);
lean_dec(v___x_851_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_876_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_asyncMode_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v_asyncMode_868_ = lean_ctor_get(v_toEnvExtension_852_, 2);
v___x_869_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_846_, v_env_853_, v_entry_845_, v_asyncMode_868_, v___x_848_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_869_);
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_messages_854_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_scopes_855_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_usedQuotCtxts_856_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v_nextMacroScope_857_);
lean_ctor_set(v_reuseFailAlloc_875_, 5, v_maxRecDepth_858_);
lean_ctor_set(v_reuseFailAlloc_875_, 6, v_ngen_859_);
lean_ctor_set(v_reuseFailAlloc_875_, 7, v_auxDeclNGen_860_);
lean_ctor_set(v_reuseFailAlloc_875_, 8, v_infoState_861_);
lean_ctor_set(v_reuseFailAlloc_875_, 9, v_traceState_862_);
lean_ctor_set(v_reuseFailAlloc_875_, 10, v_snapshotTasks_863_);
lean_ctor_set(v_reuseFailAlloc_875_, 11, v_prevLinterStates_864_);
v___x_871_ = v_reuseFailAlloc_875_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_st_ref_put(v___y_850_, v___x_871_);
v___x_873_ = lean_box(0);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___boxed(lean_object* v_mod_922_, lean_object* v_isMeta_923_, lean_object* v_hint_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v_isMeta_boxed_928_; lean_object* v_res_929_; 
v_isMeta_boxed_928_ = lean_unbox(v_isMeta_923_);
v_res_929_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_mod_922_, v_isMeta_boxed_928_, v_hint_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(lean_object* v___x_930_, lean_object* v_declName_931_, lean_object* v_as_932_, size_t v_sz_933_, size_t v_i_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
uint8_t v___x_939_; 
v___x_939_ = lean_usize_dec_lt(v_i_934_, v_sz_933_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
lean_dec(v_declName_931_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_b_935_);
return v___x_940_;
}
else
{
lean_object* v___x_941_; lean_object* v_modules_942_; lean_object* v___x_943_; lean_object* v_a_944_; lean_object* v___x_945_; lean_object* v_toImport_946_; lean_object* v_module_947_; uint8_t v___x_948_; lean_object* v___x_949_; 
v___x_941_ = l_Lean_Environment_header(v___x_930_);
v_modules_942_ = lean_ctor_get(v___x_941_, 3);
lean_inc_ref(v_modules_942_);
lean_dec_ref(v___x_941_);
v___x_943_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_944_ = lean_array_uget_borrowed(v_as_932_, v_i_934_);
v___x_945_ = lean_array_get(v___x_943_, v_modules_942_, v_a_944_);
lean_dec_ref(v_modules_942_);
v_toImport_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc_ref(v_toImport_946_);
lean_dec(v___x_945_);
v_module_947_ = lean_ctor_get(v_toImport_946_, 0);
lean_inc(v_module_947_);
lean_dec_ref(v_toImport_946_);
v___x_948_ = 0;
lean_inc(v_declName_931_);
v___x_949_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_947_, v___x_948_, v_declName_931_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v___x_950_; size_t v___x_951_; size_t v___x_952_; 
lean_dec_ref_known(v___x_949_, 1);
v___x_950_ = lean_box(0);
v___x_951_ = ((size_t)1ULL);
v___x_952_ = lean_usize_add(v_i_934_, v___x_951_);
v_i_934_ = v___x_952_;
v_b_935_ = v___x_950_;
goto _start;
}
else
{
lean_dec(v_declName_931_);
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___boxed(lean_object* v___x_954_, lean_object* v_declName_955_, lean_object* v_as_956_, lean_object* v_sz_957_, lean_object* v_i_958_, lean_object* v_b_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
size_t v_sz_boxed_963_; size_t v_i_boxed_964_; lean_object* v_res_965_; 
v_sz_boxed_963_ = lean_unbox_usize(v_sz_957_);
lean_dec(v_sz_957_);
v_i_boxed_964_ = lean_unbox_usize(v_i_958_);
lean_dec(v_i_958_);
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v___x_954_, v_declName_955_, v_as_956_, v_sz_boxed_963_, v_i_boxed_964_, v_b_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec_ref(v_as_956_);
lean_dec_ref(v___x_954_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19___redArg(lean_object* v_m_966_, lean_object* v_query_967_, lean_object* v_x_968_, lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
lean_object* v_zero_971_; uint8_t v_isZero_972_; 
v_zero_971_ = lean_unsigned_to_nat(0u);
v_isZero_972_ = lean_nat_dec_eq(v_x_969_, v_zero_971_);
if (v_isZero_972_ == 1)
{
lean_dec(v_x_970_);
lean_dec(v_x_969_);
if (lean_obj_tag(v_x_968_) == 0)
{
lean_object* v___x_973_; 
v___x_973_ = lean_box(2);
return v___x_973_;
}
else
{
lean_object* v_val_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
v_val_974_ = lean_ctor_get(v_x_968_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v_x_968_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_val_974_);
lean_dec(v_x_968_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_val_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_keyArray_982_; lean_object* v_valueArray_983_; lean_object* v___x_984_; uint8_t v_isSome_985_; 
v_keyArray_982_ = lean_ctor_get(v_m_966_, 1);
v_valueArray_983_ = lean_ctor_get(v_m_966_, 2);
v___x_984_ = lean_array_fget_borrowed(v_keyArray_982_, v_x_970_);
v_isSome_985_ = lean_noption_is_some(v___x_984_);
if (v_isSome_985_ == 0)
{
lean_dec(v_x_969_);
if (lean_obj_tag(v_x_968_) == 0)
{
lean_object* v___x_986_; 
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_x_970_);
return v___x_986_;
}
else
{
lean_object* v_val_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec(v_x_970_);
v_val_987_ = lean_ctor_get(v_x_968_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v_x_968_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_val_987_);
lean_dec(v_x_968_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_val_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v_one_995_; lean_object* v_n_996_; lean_object* v___y_998_; 
v_one_995_ = lean_unsigned_to_nat(1u);
v_n_996_ = lean_nat_sub(v_x_969_, v_one_995_);
lean_dec(v_x_969_);
if (v_isSome_985_ == 0)
{
goto v___jp_1004_;
}
else
{
lean_object* v___x_1006_; uint8_t v_isSome_1007_; 
v___x_1006_ = lean_array_fget_borrowed(v_valueArray_983_, v_x_970_);
v_isSome_1007_ = lean_noption_is_some(v___x_1006_);
if (v_isSome_1007_ == 0)
{
goto v___jp_1004_;
}
else
{
lean_object* v_val_1008_; uint8_t v___x_1009_; 
lean_inc(v___x_984_);
v_val_1008_ = lean_noption_get(v___x_984_);
v___x_1009_ = lean_name_eq(v_val_1008_, v_query_967_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
lean_dec(v_val_1008_);
v___x_1010_ = lean_array_get_size(v_keyArray_982_);
v___x_1011_ = lean_nat_add(v_x_970_, v_one_995_);
lean_dec(v_x_970_);
v___x_1012_ = lean_nat_dec_lt(v___x_1011_, v___x_1010_);
if (v___x_1012_ == 0)
{
lean_dec(v___x_1011_);
v_x_969_ = v_n_996_;
v_x_970_ = v_zero_971_;
goto _start;
}
else
{
v_x_969_ = v_n_996_;
v_x_970_ = v___x_1011_;
goto _start;
}
}
else
{
lean_object* v_val_1015_; lean_object* v___x_1016_; 
lean_dec(v_n_996_);
lean_dec(v_x_968_);
lean_inc(v___x_1006_);
v_val_1015_ = lean_noption_get(v___x_1006_);
v___x_1016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1016_, 0, v_x_970_);
lean_ctor_set(v___x_1016_, 1, v_val_1008_);
lean_ctor_set(v___x_1016_, 2, v_val_1015_);
return v___x_1016_;
}
}
}
v___jp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_999_ = lean_array_get_size(v_keyArray_982_);
v___x_1000_ = lean_nat_add(v_x_970_, v_one_995_);
lean_dec(v_x_970_);
v___x_1001_ = lean_nat_dec_lt(v___x_1000_, v___x_999_);
if (v___x_1001_ == 0)
{
lean_dec(v___x_1000_);
v_x_968_ = v___y_998_;
v_x_969_ = v_n_996_;
v_x_970_ = v_zero_971_;
goto _start;
}
else
{
v_x_968_ = v___y_998_;
v_x_969_ = v_n_996_;
v_x_970_ = v___x_1000_;
goto _start;
}
}
v___jp_1004_:
{
if (lean_obj_tag(v_x_968_) == 0)
{
lean_object* v___x_1005_; 
lean_inc(v_x_970_);
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_x_970_);
v___y_998_ = v___x_1005_;
goto v___jp_997_;
}
else
{
v___y_998_ = v_x_968_;
goto v___jp_997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19___redArg___boxed(lean_object* v_m_1017_, lean_object* v_query_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19___redArg(v_m_1017_, v_query_1018_, v_x_1019_, v_x_1020_, v_x_1021_);
lean_dec(v_query_1018_);
lean_dec_ref(v_m_1017_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16___redArg(lean_object* v_m_1023_, lean_object* v_query_1024_){
_start:
{
lean_object* v_keyArray_1025_; lean_object* v___x_1026_; uint64_t v___y_1028_; 
v_keyArray_1025_ = lean_ctor_get(v_m_1023_, 1);
v___x_1026_ = lean_array_get_size(v_keyArray_1025_);
if (lean_obj_tag(v_query_1024_) == 0)
{
uint64_t v___x_1043_; 
v___x_1043_ = 1723ULL;
v___y_1028_ = v___x_1043_;
goto v___jp_1027_;
}
else
{
uint64_t v_hash_1044_; 
v_hash_1044_ = lean_ctor_get_uint64(v_query_1024_, sizeof(void*)*2);
v___y_1028_ = v_hash_1044_;
goto v___jp_1027_;
}
v___jp_1027_:
{
uint64_t v___x_1029_; uint64_t v___x_1030_; uint64_t v_fold_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1029_ = 32ULL;
v___x_1030_ = lean_uint64_shift_right(v___y_1028_, v___x_1029_);
v_fold_1031_ = lean_uint64_xor(v___y_1028_, v___x_1030_);
v___x_1032_ = 16ULL;
v___x_1033_ = lean_uint64_shift_right(v_fold_1031_, v___x_1032_);
v___x_1034_ = lean_uint64_xor(v_fold_1031_, v___x_1033_);
v___x_1035_ = lean_uint64_to_usize(v___x_1034_);
v___x_1036_ = lean_usize_of_nat(v___x_1026_);
v___x_1037_ = ((size_t)1ULL);
v___x_1038_ = lean_usize_sub(v___x_1036_, v___x_1037_);
v___x_1039_ = lean_usize_land(v___x_1035_, v___x_1038_);
v___x_1040_ = lean_usize_to_nat(v___x_1039_);
v___x_1041_ = lean_box(0);
v___x_1042_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19___redArg(v_m_1023_, v_query_1024_, v___x_1041_, v___x_1026_, v___x_1040_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16___redArg___boxed(lean_object* v_m_1045_, lean_object* v_query_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16___redArg(v_m_1045_, v_query_1046_);
lean_dec(v_query_1046_);
lean_dec_ref(v_m_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_m_1048_, lean_object* v_query_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16___redArg(v_m_1048_, v_query_1049_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_index_1051_; lean_object* v_key_1052_; lean_object* v_value_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_index_1051_ = lean_ctor_get(v___x_1050_, 0);
v_key_1052_ = lean_ctor_get(v___x_1050_, 1);
v_value_1053_ = lean_ctor_get(v___x_1050_, 2);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1050_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_value_1053_);
lean_inc(v_key_1052_);
lean_inc(v_index_1051_);
lean_dec(v___x_1050_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_index_1051_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_key_1052_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v_value_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v___x_1061_; 
lean_dec(v___x_1050_);
v___x_1061_ = lean_box(1);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_m_1062_, lean_object* v_query_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_m_1062_, v_query_1063_);
lean_dec(v_query_1063_);
lean_dec_ref(v_m_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(lean_object* v_m_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_m_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_value_1068_; lean_object* v___x_1069_; 
v_value_1068_ = lean_ctor_get(v___x_1067_, 2);
lean_inc(v_value_1068_);
lean_dec_ref_known(v___x_1067_, 3);
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_value_1068_);
return v___x_1069_;
}
else
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_box(0);
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_m_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_m_1071_);
return v_res_1073_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1));
v___x_1077_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0));
v___x_1078_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1077_, v___x_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(lean_object* v_declName_1081_, uint8_t v_isMeta_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; lean_object* v_env_1090_; lean_object* v___y_1092_; lean_object* v___x_1105_; 
v___x_1086_ = lean_st_ref_get(v___y_1084_);
v_env_1090_ = lean_ctor_get(v___x_1086_, 0);
lean_inc_ref(v_env_1090_);
lean_dec(v___x_1086_);
v___x_1105_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1090_, v_declName_1081_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_dec_ref(v_env_1090_);
lean_dec(v_declName_1081_);
goto v___jp_1087_;
}
else
{
lean_object* v_val_1106_; lean_object* v___x_1107_; lean_object* v_modules_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_val_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_val_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1107_ = l_Lean_Environment_header(v_env_1090_);
v_modules_1108_ = lean_ctor_get(v___x_1107_, 3);
lean_inc_ref(v_modules_1108_);
lean_dec_ref(v___x_1107_);
v___x_1109_ = lean_array_get_size(v_modules_1108_);
v___x_1110_ = lean_nat_dec_lt(v_val_1106_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_dec_ref(v_modules_1108_);
lean_dec(v_val_1106_);
lean_dec_ref(v_env_1090_);
lean_dec(v_declName_1081_);
goto v___jp_1087_;
}
else
{
lean_object* v___x_1111_; lean_object* v_env_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___y_1116_; 
v___x_1111_ = lean_st_ref_get(v___y_1084_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2);
v___x_1114_ = lean_array_fget(v_modules_1108_, v_val_1106_);
lean_dec(v_val_1106_);
lean_dec_ref(v_modules_1108_);
if (v_isMeta_1082_ == 0)
{
lean_dec_ref(v_env_1112_);
v___y_1116_ = v_isMeta_1082_;
goto v___jp_1115_;
}
else
{
uint8_t v___x_1127_; 
lean_inc(v_declName_1081_);
v___x_1127_ = l_Lean_isMarkedMeta(v_env_1112_, v_declName_1081_);
if (v___x_1127_ == 0)
{
v___y_1116_ = v_isMeta_1082_;
goto v___jp_1115_;
}
else
{
uint8_t v___x_1128_; 
v___x_1128_ = 0;
v___y_1116_ = v___x_1128_;
goto v___jp_1115_;
}
}
v___jp_1115_:
{
lean_object* v_toImport_1117_; lean_object* v_module_1118_; lean_object* v___x_1119_; 
v_toImport_1117_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_toImport_1117_);
lean_dec(v___x_1114_);
v_module_1118_ = lean_ctor_get(v_toImport_1117_, 0);
lean_inc(v_module_1118_);
lean_dec_ref(v_toImport_1117_);
lean_inc(v_declName_1081_);
v___x_1119_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_1118_, v___y_1116_, v_declName_1081_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec_ref_known(v___x_1119_, 1);
v___x_1120_ = l_Lean_indirectModUseExt;
v___x_1121_ = lean_box(1);
v___x_1122_ = lean_box(0);
lean_inc_ref(v_env_1090_);
v___x_1123_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1113_, v___x_1120_, v_env_1090_, v___x_1121_, v___x_1122_);
v___x_1124_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v___x_1123_, v_declName_1081_);
lean_dec(v___x_1123_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3));
v___y_1092_ = v___x_1125_;
goto v___jp_1091_;
}
else
{
lean_object* v_val_1126_; 
v_val_1126_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_val_1126_);
lean_dec_ref_known(v___x_1124_, 1);
v___y_1092_ = v_val_1126_;
goto v___jp_1091_;
}
}
else
{
lean_dec_ref(v_env_1090_);
lean_dec(v_declName_1081_);
return v___x_1119_;
}
}
}
}
v___jp_1087_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
v___jp_1091_:
{
lean_object* v___x_1093_; size_t v_sz_1094_; size_t v___x_1095_; lean_object* v___x_1096_; 
v___x_1093_ = lean_box(0);
v_sz_1094_ = lean_array_size(v___y_1092_);
v___x_1095_ = ((size_t)0ULL);
v___x_1096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v_env_1090_, v_declName_1081_, v___y_1092_, v_sz_1094_, v___x_1095_, v___x_1093_, v___y_1083_, v___y_1084_);
lean_dec_ref(v___y_1092_);
lean_dec_ref(v_env_1090_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; 
v_unused_1104_ = lean_ctor_get(v___x_1096_, 0);
lean_dec(v_unused_1104_);
v___x_1098_ = v___x_1096_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_dec(v___x_1096_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1093_);
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1093_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
else
{
return v___x_1096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___boxed(lean_object* v_declName_1129_, lean_object* v_isMeta_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
uint8_t v_isMeta_boxed_1134_; lean_object* v_res_1135_; 
v_isMeta_boxed_1134_ = lean_unbox(v_isMeta_1130_);
v_res_1135_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_declName_1129_, v_isMeta_boxed_1134_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(lean_object* v_as_x27_1136_, lean_object* v_b_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
if (lean_obj_tag(v_as_x27_1136_) == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_b_1137_);
return v___x_1141_;
}
else
{
lean_object* v_head_1142_; lean_object* v_tail_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
v_head_1142_ = lean_ctor_get(v_as_x27_1136_, 0);
v_tail_1143_ = lean_ctor_get(v_as_x27_1136_, 1);
v___x_1144_ = 1;
lean_inc(v_head_1142_);
v___x_1145_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_head_1142_, v___x_1144_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1146_; 
lean_dec_ref_known(v___x_1145_, 1);
v___x_1146_ = lean_box(0);
v_as_x27_1136_ = v_tail_1143_;
v_b_1137_ = v___x_1146_;
goto _start;
}
else
{
return v___x_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg___boxed(lean_object* v_as_x27_1148_, lean_object* v_b_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_1148_, v_b_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v_as_x27_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(lean_object* v_as_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
if (lean_obj_tag(v_as_1154_) == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
else
{
lean_object* v_head_1160_; lean_object* v_tail_1161_; lean_object* v_fst_1162_; lean_object* v_snd_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_scopes_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_opts_1170_; uint8_t v_hasTrace_1171_; 
v_head_1160_ = lean_ctor_get(v_as_1154_, 0);
lean_inc(v_head_1160_);
v_tail_1161_ = lean_ctor_get(v_as_1154_, 1);
lean_inc(v_tail_1161_);
lean_dec_ref_known(v_as_1154_, 2);
v_fst_1162_ = lean_ctor_get(v_head_1160_, 0);
lean_inc(v_fst_1162_);
v_snd_1163_ = lean_ctor_get(v_head_1160_, 1);
lean_inc(v_snd_1163_);
lean_dec(v_head_1160_);
v___x_1164_ = l_Lean_inheritedTraceOptions;
v___x_1165_ = lean_st_ref_get(v___x_1164_);
v___x_1166_ = lean_st_ref_get(v___y_1156_);
v_scopes_1167_ = lean_ctor_get(v___x_1166_, 2);
lean_inc(v_scopes_1167_);
lean_dec(v___x_1166_);
v___x_1168_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1169_ = l_List_head_x21___redArg(v___x_1168_, v_scopes_1167_);
lean_dec(v_scopes_1167_);
v_opts_1170_ = lean_ctor_get(v___x_1169_, 1);
lean_inc_ref(v_opts_1170_);
lean_dec(v___x_1169_);
v_hasTrace_1171_ = lean_ctor_get_uint8(v_opts_1170_, sizeof(void*)*1);
if (v_hasTrace_1171_ == 0)
{
lean_dec_ref(v_opts_1170_);
lean_dec(v___x_1165_);
lean_dec(v_snd_1163_);
lean_dec(v_fst_1162_);
v_as_1154_ = v_tail_1161_;
goto _start;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1173_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11));
lean_inc(v_fst_1162_);
v___x_1174_ = l_Lean_Name_append(v___x_1173_, v_fst_1162_);
v___x_1175_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1165_, v_opts_1170_, v___x_1174_);
lean_dec(v___x_1174_);
lean_dec_ref(v_opts_1170_);
lean_dec(v___x_1165_);
if (v___x_1175_ == 0)
{
lean_dec(v_snd_1163_);
lean_dec(v_fst_1162_);
v_as_1154_ = v_tail_1161_;
goto _start;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_snd_1163_);
v___x_1178_ = l_Lean_MessageData_ofFormat(v___x_1177_);
v___x_1179_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_fst_1162_, v___x_1178_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_dec_ref_known(v___x_1179_, 1);
v_as_1154_ = v_tail_1161_;
goto _start;
}
else
{
lean_dec(v_tail_1161_);
return v___x_1179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3___boxed(lean_object* v_as_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v_as_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
return v_res_1185_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(lean_object* v_opts_1186_, lean_object* v_opt_1187_){
_start:
{
lean_object* v_name_1188_; lean_object* v_defValue_1189_; lean_object* v_map_1190_; lean_object* v___x_1191_; 
v_name_1188_ = lean_ctor_get(v_opt_1187_, 0);
v_defValue_1189_ = lean_ctor_get(v_opt_1187_, 1);
v_map_1190_ = lean_ctor_get(v_opts_1186_, 0);
v___x_1191_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1190_, v_name_1188_);
if (lean_obj_tag(v___x_1191_) == 0)
{
uint8_t v___x_1192_; 
v___x_1192_ = lean_unbox(v_defValue_1189_);
return v___x_1192_;
}
else
{
lean_object* v_val_1193_; 
v_val_1193_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_val_1193_);
lean_dec_ref_known(v___x_1191_, 1);
if (lean_obj_tag(v_val_1193_) == 1)
{
uint8_t v_v_1194_; 
v_v_1194_ = lean_ctor_get_uint8(v_val_1193_, 0);
lean_dec_ref_known(v_val_1193_, 0);
return v_v_1194_;
}
else
{
uint8_t v___x_1195_; 
lean_dec(v_val_1193_);
v___x_1195_ = lean_unbox(v_defValue_1189_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___boxed(lean_object* v_opts_1196_, lean_object* v_opt_1197_){
_start:
{
uint8_t v_res_1198_; lean_object* v_r_1199_; 
v_res_1198_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(v_opts_1196_, v_opt_1197_);
lean_dec_ref(v_opt_1197_);
lean_dec_ref(v_opts_1196_);
v_r_1199_ = lean_box(v_res_1198_);
return v_r_1199_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_box(1);
v___x_1201_ = l_Lean_MessageData_ofFormat(v___x_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__3(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__2));
v___x_1206_ = l_Lean_MessageData_ofFormat(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20(lean_object* v_x_1207_, lean_object* v_x_1208_){
_start:
{
if (lean_obj_tag(v_x_1208_) == 0)
{
return v_x_1207_;
}
else
{
lean_object* v_head_1209_; lean_object* v_tail_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1232_; 
v_head_1209_ = lean_ctor_get(v_x_1208_, 0);
v_tail_1210_ = lean_ctor_get(v_x_1208_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_x_1208_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1212_ = v_x_1208_;
v_isShared_1213_ = v_isSharedCheck_1232_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_tail_1210_);
lean_inc(v_head_1209_);
lean_dec(v_x_1208_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1232_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_before_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1230_; 
v_before_1214_ = lean_ctor_get(v_head_1209_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_head_1209_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_head_1209_, 1);
lean_dec(v_unused_1231_);
v___x_1216_ = v_head_1209_;
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_before_1214_);
lean_dec(v_head_1209_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__0);
if (v_isShared_1217_ == 0)
{
lean_ctor_set_tag(v___x_1216_, 7);
lean_ctor_set(v___x_1216_, 1, v___x_1218_);
lean_ctor_set(v___x_1216_, 0, v_x_1207_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_x_1207_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__3);
if (v_isShared_1213_ == 0)
{
lean_ctor_set_tag(v___x_1212_, 7);
lean_ctor_set(v___x_1212_, 1, v___x_1221_);
lean_ctor_set(v___x_1212_, 0, v___x_1220_);
v___x_1223_ = v___x_1212_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = l_Lean_MessageData_ofSyntax(v_before_1214_);
v___x_1225_ = l_Lean_indentD(v___x_1224_);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1223_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v_x_1207_ = v___x_1226_;
v_x_1208_ = v_tail_1210_;
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
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1));
v___x_1237_ = l_Lean_MessageData_ofFormat(v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(lean_object* v_msgData_1238_, lean_object* v_macroStack_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; lean_object* v_scopes_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_opts_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1242_ = lean_st_ref_get(v___y_1240_);
v_scopes_1243_ = lean_ctor_get(v___x_1242_, 2);
lean_inc(v_scopes_1243_);
lean_dec(v___x_1242_);
v___x_1244_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1245_ = l_List_head_x21___redArg(v___x_1244_, v_scopes_1243_);
lean_dec(v_scopes_1243_);
v_opts_1246_ = lean_ctor_get(v___x_1245_, 1);
lean_inc_ref(v_opts_1246_);
lean_dec(v___x_1245_);
v___x_1247_ = l_Lean_Elab_pp_macroStack;
v___x_1248_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(v_opts_1246_, v___x_1247_);
lean_dec_ref(v_opts_1246_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
lean_dec(v_macroStack_1239_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_msgData_1238_);
return v___x_1249_;
}
else
{
if (lean_obj_tag(v_macroStack_1239_) == 0)
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v_msgData_1238_);
return v___x_1250_;
}
else
{
lean_object* v_head_1251_; lean_object* v_after_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1267_; 
v_head_1251_ = lean_ctor_get(v_macroStack_1239_, 0);
lean_inc(v_head_1251_);
v_after_1252_ = lean_ctor_get(v_head_1251_, 1);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_head_1251_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v_head_1251_, 0);
lean_dec(v_unused_1268_);
v___x_1254_ = v_head_1251_;
v_isShared_1255_ = v_isSharedCheck_1267_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_after_1252_);
lean_dec(v_head_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1267_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1256_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20___closed__0);
if (v_isShared_1255_ == 0)
{
lean_ctor_set_tag(v___x_1254_, 7);
lean_ctor_set(v___x_1254_, 1, v___x_1256_);
lean_ctor_set(v___x_1254_, 0, v_msgData_1238_);
v___x_1258_ = v___x_1254_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_msgData_1238_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v_msgData_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1259_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Lean_MessageData_ofSyntax(v_after_1252_);
v___x_1262_ = l_Lean_indentD(v___x_1261_);
v_msgData_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1263_, 0, v___x_1260_);
lean_ctor_set(v_msgData_1263_, 1, v___x_1262_);
v___x_1264_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__20(v_msgData_1263_, v_macroStack_1239_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___boxed(lean_object* v_msgData_1269_, lean_object* v_macroStack_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_1269_, v_macroStack_1270_, v___y_1271_);
lean_dec(v___y_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(lean_object* v_msg_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Elab_Command_getRef___redArg(v___y_1275_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v_macroStack_1280_; lean_object* v___x_1281_; lean_object* v_a_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1293_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v_macroStack_1280_ = lean_ctor_get(v___y_1275_, 4);
v___x_1281_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_1274_, v___y_1276_);
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = l_Lean_Elab_getBetterRef(v_a_1279_, v_macroStack_1280_);
lean_dec(v_a_1279_);
lean_inc(v_macroStack_1280_);
v___x_1284_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_a_1282_, v_macroStack_1280_, v___y_1276_);
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1283_);
lean_ctor_set(v___x_1289_, 1, v_a_1285_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set_tag(v___x_1287_, 1);
lean_ctor_set(v___x_1287_, 0, v___x_1289_);
v___x_1291_ = v___x_1287_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v_msg_1274_);
v_a_1294_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1278_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1278_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg___boxed(lean_object* v_msg_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(lean_object* v_ref_1307_, lean_object* v_msg_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Elab_Command_getRef___redArg(v___y_1309_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v_fileName_1314_; lean_object* v_fileMap_1315_; lean_object* v_currRecDepth_1316_; lean_object* v_cmdPos_1317_; lean_object* v_macroStack_1318_; lean_object* v_quotContext_x3f_1319_; lean_object* v_currMacroScope_1320_; lean_object* v_snap_x3f_1321_; lean_object* v_cancelTk_x3f_1322_; uint8_t v_suppressElabErrors_1323_; lean_object* v_ref_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v_fileName_1314_ = lean_ctor_get(v___y_1309_, 0);
v_fileMap_1315_ = lean_ctor_get(v___y_1309_, 1);
v_currRecDepth_1316_ = lean_ctor_get(v___y_1309_, 2);
v_cmdPos_1317_ = lean_ctor_get(v___y_1309_, 3);
v_macroStack_1318_ = lean_ctor_get(v___y_1309_, 4);
v_quotContext_x3f_1319_ = lean_ctor_get(v___y_1309_, 5);
v_currMacroScope_1320_ = lean_ctor_get(v___y_1309_, 6);
v_snap_x3f_1321_ = lean_ctor_get(v___y_1309_, 8);
v_cancelTk_x3f_1322_ = lean_ctor_get(v___y_1309_, 9);
v_suppressElabErrors_1323_ = lean_ctor_get_uint8(v___y_1309_, sizeof(void*)*10);
v_ref_1324_ = l_Lean_replaceRef(v_ref_1307_, v_a_1313_);
lean_dec(v_a_1313_);
lean_inc(v_cancelTk_x3f_1322_);
lean_inc(v_snap_x3f_1321_);
lean_inc(v_currMacroScope_1320_);
lean_inc(v_quotContext_x3f_1319_);
lean_inc(v_macroStack_1318_);
lean_inc(v_cmdPos_1317_);
lean_inc(v_currRecDepth_1316_);
lean_inc_ref(v_fileMap_1315_);
lean_inc_ref(v_fileName_1314_);
v___x_1325_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1325_, 0, v_fileName_1314_);
lean_ctor_set(v___x_1325_, 1, v_fileMap_1315_);
lean_ctor_set(v___x_1325_, 2, v_currRecDepth_1316_);
lean_ctor_set(v___x_1325_, 3, v_cmdPos_1317_);
lean_ctor_set(v___x_1325_, 4, v_macroStack_1318_);
lean_ctor_set(v___x_1325_, 5, v_quotContext_x3f_1319_);
lean_ctor_set(v___x_1325_, 6, v_currMacroScope_1320_);
lean_ctor_set(v___x_1325_, 7, v_ref_1324_);
lean_ctor_set(v___x_1325_, 8, v_snap_x3f_1321_);
lean_ctor_set(v___x_1325_, 9, v_cancelTk_x3f_1322_);
lean_ctor_set_uint8(v___x_1325_, sizeof(void*)*10, v_suppressElabErrors_1323_);
v___x_1326_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1308_, v___x_1325_, v___y_1310_);
lean_dec_ref_known(v___x_1325_, 10);
return v___x_1326_;
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_msg_1308_);
v_a_1327_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1312_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1312_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1335_, lean_object* v_msg_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_1335_, v_msg_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v_ref_1335_);
return v_res_1340_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v___x_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg(){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0);
v___x_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___boxed(lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(lean_object* v_env_1349_, lean_object* v_opts_1350_, lean_object* v_currNamespace_1351_, lean_object* v_openDecls_1352_, lean_object* v_n_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = l_Lean_ResolveName_resolveGlobalName(v_env_1349_, v_opts_1350_, v_currNamespace_1351_, v_openDecls_1352_, v_n_1353_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v___y_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed(lean_object* v_env_1358_, lean_object* v_opts_1359_, lean_object* v_currNamespace_1360_, lean_object* v_openDecls_1361_, lean_object* v_n_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(v_env_1358_, v_opts_1359_, v_currNamespace_1360_, v_openDecls_1361_, v_n_1362_, v___y_1363_, v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec_ref(v_opts_1359_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(lean_object* v_x_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; lean_object* v_env_1372_; lean_object* v___x_1373_; lean_object* v_scopes_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_opts_1377_; lean_object* v___x_1378_; 
v___x_1371_ = lean_st_ref_get(v___y_1369_);
v_env_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc_ref(v_env_1372_);
lean_dec(v___x_1371_);
v___x_1373_ = lean_st_ref_get(v___y_1369_);
v_scopes_1374_ = lean_ctor_get(v___x_1373_, 2);
lean_inc(v_scopes_1374_);
lean_dec(v___x_1373_);
v___x_1375_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1376_ = l_List_head_x21___redArg(v___x_1375_, v_scopes_1374_);
lean_dec(v_scopes_1374_);
v_opts_1377_ = lean_ctor_get(v___x_1376_, 1);
lean_inc_ref(v_opts_1377_);
lean_dec(v___x_1376_);
v___x_1378_ = l_Lean_Elab_Command_getScope___redArg(v___y_1369_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v_currNamespace_1380_; lean_object* v___x_1381_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v_currNamespace_1380_ = lean_ctor_get(v_a_1379_, 2);
lean_inc(v_currNamespace_1380_);
lean_dec(v_a_1379_);
v___x_1381_ = l_Lean_Elab_Command_getScope___redArg(v___y_1369_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v_openDecls_1383_; lean_object* v___x_1384_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v_openDecls_1383_ = lean_ctor_get(v_a_1382_, 3);
lean_inc(v_openDecls_1383_);
lean_dec(v_a_1382_);
v___x_1384_ = l_Lean_Elab_Command_getRef___redArg(v___y_1368_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1368_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v_currRecDepth_1388_; lean_object* v_quotContext_x3f_1389_; lean_object* v___f_1390_; lean_object* v___f_1391_; lean_object* v___f_1392_; lean_object* v___f_1393_; lean_object* v___f_1394_; lean_object* v_methods_1395_; lean_object* v_a_1397_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v_currRecDepth_1388_ = lean_ctor_get(v___y_1368_, 2);
v_quotContext_x3f_1389_ = lean_ctor_get(v___y_1368_, 5);
lean_inc_ref_n(v_env_1372_, 3);
v___f_1390_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1390_, 0, v_env_1372_);
v___f_1391_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1391_, 0, v_env_1372_);
lean_inc_n(v_currNamespace_1380_, 2);
v___f_1392_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1392_, 0, v_currNamespace_1380_);
lean_inc(v_openDecls_1383_);
v___f_1393_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1393_, 0, v_env_1372_);
lean_closure_set(v___f_1393_, 1, v_currNamespace_1380_);
lean_closure_set(v___f_1393_, 2, v_openDecls_1383_);
v___f_1394_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1394_, 0, v_env_1372_);
lean_closure_set(v___f_1394_, 1, v_opts_1377_);
lean_closure_set(v___f_1394_, 2, v_currNamespace_1380_);
lean_closure_set(v___f_1394_, 3, v_openDecls_1383_);
v_methods_1395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1395_, 0, v___f_1391_);
lean_ctor_set(v_methods_1395_, 1, v___f_1392_);
lean_ctor_set(v_methods_1395_, 2, v___f_1390_);
lean_ctor_set(v_methods_1395_, 3, v___f_1393_);
lean_ctor_set(v_methods_1395_, 4, v___f_1394_);
if (lean_obj_tag(v_quotContext_x3f_1389_) == 0)
{
lean_object* v___x_1470_; lean_object* v_a_1471_; 
v___x_1470_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_1369_);
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref(v___x_1470_);
v_a_1397_ = v_a_1471_;
goto v___jp_1396_;
}
else
{
lean_object* v_val_1472_; 
v_val_1472_ = lean_ctor_get(v_quotContext_x3f_1389_, 0);
lean_inc(v_val_1472_);
v_a_1397_ = v_val_1472_;
goto v___jp_1396_;
}
v___jp_1396_:
{
lean_object* v___x_1398_; lean_object* v_maxRecDepth_1399_; lean_object* v___x_1400_; lean_object* v_nextMacroScope_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1398_ = lean_st_ref_get(v___y_1369_);
v_maxRecDepth_1399_ = lean_ctor_get(v___x_1398_, 5);
lean_inc(v_maxRecDepth_1399_);
lean_dec(v___x_1398_);
v___x_1400_ = lean_st_ref_get(v___y_1369_);
v_nextMacroScope_1401_ = lean_ctor_get(v___x_1400_, 4);
lean_inc(v_nextMacroScope_1401_);
lean_dec(v___x_1400_);
lean_inc(v_currRecDepth_1388_);
v___x_1402_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1402_, 0, v_methods_1395_);
lean_ctor_set(v___x_1402_, 1, v_a_1397_);
lean_ctor_set(v___x_1402_, 2, v_a_1387_);
lean_ctor_set(v___x_1402_, 3, v_currRecDepth_1388_);
lean_ctor_set(v___x_1402_, 4, v_maxRecDepth_1399_);
lean_ctor_set(v___x_1402_, 5, v_a_1385_);
v___x_1403_ = lean_box(0);
v___x_1404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1404_, 0, v_nextMacroScope_1401_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
lean_ctor_set(v___x_1404_, 2, v___x_1403_);
v___x_1405_ = lean_apply_2(v_x_1367_, v___x_1402_, v___x_1404_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v_a_1407_; lean_object* v_macroScope_1408_; lean_object* v_traceMsgs_1409_; lean_object* v_expandedMacroDecls_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_a_1406_);
v_a_1407_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1405_, 2);
v_macroScope_1408_ = lean_ctor_get(v_a_1406_, 0);
lean_inc(v_macroScope_1408_);
v_traceMsgs_1409_ = lean_ctor_get(v_a_1406_, 1);
lean_inc(v_traceMsgs_1409_);
v_expandedMacroDecls_1410_ = lean_ctor_get(v_a_1406_, 2);
lean_inc(v_expandedMacroDecls_1410_);
lean_dec(v_a_1406_);
v___x_1411_ = lean_box(0);
v___x_1412_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_expandedMacroDecls_1410_, v___x_1411_, v___y_1368_, v___y_1369_);
lean_dec(v_expandedMacroDecls_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1413_; lean_object* v_env_1414_; lean_object* v_messages_1415_; lean_object* v_scopes_1416_; lean_object* v_usedQuotCtxts_1417_; lean_object* v_maxRecDepth_1418_; lean_object* v_ngen_1419_; lean_object* v_auxDeclNGen_1420_; lean_object* v_infoState_1421_; lean_object* v_traceState_1422_; lean_object* v_snapshotTasks_1423_; lean_object* v_prevLinterStates_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref_known(v___x_1412_, 1);
v___x_1413_ = lean_st_ref_take(v___y_1369_);
v_env_1414_ = lean_ctor_get(v___x_1413_, 0);
v_messages_1415_ = lean_ctor_get(v___x_1413_, 1);
v_scopes_1416_ = lean_ctor_get(v___x_1413_, 2);
v_usedQuotCtxts_1417_ = lean_ctor_get(v___x_1413_, 3);
v_maxRecDepth_1418_ = lean_ctor_get(v___x_1413_, 5);
v_ngen_1419_ = lean_ctor_get(v___x_1413_, 6);
v_auxDeclNGen_1420_ = lean_ctor_get(v___x_1413_, 7);
v_infoState_1421_ = lean_ctor_get(v___x_1413_, 8);
v_traceState_1422_ = lean_ctor_get(v___x_1413_, 9);
v_snapshotTasks_1423_ = lean_ctor_get(v___x_1413_, 10);
v_prevLinterStates_1424_ = lean_ctor_get(v___x_1413_, 11);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v___x_1413_, 4);
lean_dec(v_unused_1451_);
v___x_1426_ = v___x_1413_;
v_isShared_1427_ = v_isSharedCheck_1450_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_prevLinterStates_1424_);
lean_inc(v_snapshotTasks_1423_);
lean_inc(v_traceState_1422_);
lean_inc(v_infoState_1421_);
lean_inc(v_auxDeclNGen_1420_);
lean_inc(v_ngen_1419_);
lean_inc(v_maxRecDepth_1418_);
lean_inc(v_usedQuotCtxts_1417_);
lean_inc(v_scopes_1416_);
lean_inc(v_messages_1415_);
lean_inc(v_env_1414_);
lean_dec(v___x_1413_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1450_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 4, v_macroScope_1408_);
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_env_1414_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_messages_1415_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v_scopes_1416_);
lean_ctor_set(v_reuseFailAlloc_1449_, 3, v_usedQuotCtxts_1417_);
lean_ctor_set(v_reuseFailAlloc_1449_, 4, v_macroScope_1408_);
lean_ctor_set(v_reuseFailAlloc_1449_, 5, v_maxRecDepth_1418_);
lean_ctor_set(v_reuseFailAlloc_1449_, 6, v_ngen_1419_);
lean_ctor_set(v_reuseFailAlloc_1449_, 7, v_auxDeclNGen_1420_);
lean_ctor_set(v_reuseFailAlloc_1449_, 8, v_infoState_1421_);
lean_ctor_set(v_reuseFailAlloc_1449_, 9, v_traceState_1422_);
lean_ctor_set(v_reuseFailAlloc_1449_, 10, v_snapshotTasks_1423_);
lean_ctor_set(v_reuseFailAlloc_1449_, 11, v_prevLinterStates_1424_);
v___x_1429_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_st_ref_put(v___y_1369_, v___x_1429_);
v___x_1431_ = l_List_reverse___redArg(v_traceMsgs_1409_);
v___x_1432_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v___x_1431_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v___x_1432_, 0);
lean_dec(v_unused_1440_);
v___x_1434_ = v___x_1432_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_dec(v___x_1432_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v_a_1407_);
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1407_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_a_1407_);
v_a_1441_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1432_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1432_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_traceMsgs_1409_);
lean_dec(v_macroScope_1408_);
lean_dec(v_a_1407_);
v_a_1452_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1412_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1412_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1460_; 
v_a_1460_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1405_, 2);
if (lean_obj_tag(v_a_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v_a_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_a_1461_ = lean_ctor_get(v_a_1460_, 0);
lean_inc(v_a_1461_);
v_a_1462_ = lean_ctor_get(v_a_1460_, 1);
lean_inc_ref(v_a_1462_);
lean_dec_ref_known(v_a_1460_, 2);
v___x_1463_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0));
v___x_1464_ = lean_string_dec_eq(v_a_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_a_1462_);
v___x_1466_ = l_Lean_MessageData_ofFormat(v___x_1465_);
v___x_1467_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_a_1461_, v___x_1466_, v___y_1368_, v___y_1369_);
lean_dec(v_a_1461_);
return v___x_1467_;
}
else
{
lean_object* v___x_1468_; 
lean_dec_ref(v_a_1462_);
v___x_1468_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_a_1461_);
return v___x_1468_;
}
}
else
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v___x_1469_;
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_a_1385_);
lean_dec(v_openDecls_1383_);
lean_dec(v_currNamespace_1380_);
lean_dec_ref(v_opts_1377_);
lean_dec_ref(v_env_1372_);
lean_dec_ref(v_x_1367_);
v_a_1473_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1386_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1386_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v_openDecls_1383_);
lean_dec(v_currNamespace_1380_);
lean_dec_ref(v_opts_1377_);
lean_dec_ref(v_env_1372_);
lean_dec_ref(v_x_1367_);
v_a_1481_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1384_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1384_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v_currNamespace_1380_);
lean_dec_ref(v_opts_1377_);
lean_dec_ref(v_env_1372_);
lean_dec_ref(v_x_1367_);
v_a_1489_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1381_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1381_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec_ref(v_opts_1377_);
lean_dec_ref(v_env_1372_);
lean_dec_ref(v_x_1367_);
v_a_1497_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1378_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1378_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___boxed(lean_object* v_x_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v_x_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
return v_res_1509_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1525_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11));
v___x_1526_ = l_Lean_Name_append(v___x_1525_, v___x_1524_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__8));
v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__10));
v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object* v_modifiers_1533_, lean_object* v_stx_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v_declId_1545_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1558_ = l_Lean_Syntax_getArg(v_stx_1534_, v___x_1538_);
v___x_1559_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_1559_, 0, v___x_1558_);
v___x_1560_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_1559_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = lean_unsigned_to_nat(2u);
v___x_1585_ = l_Lean_Syntax_getArg(v_stx_1534_, v___x_1562_);
v___x_1586_ = lean_alloc_closure((void*)(l_Lean_Elab_expandOptNamedPrio___boxed), 3, 1);
lean_closure_set(v___x_1586_, 0, v___x_1585_);
v___x_1587_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_1586_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = l_Lean_Elab_Command_getRef___redArg(v_a_1535_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1535_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_quotContext_x3f_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; 
lean_dec_ref_known(v___x_1591_, 1);
v_quotContext_x3f_1592_ = lean_ctor_get(v_a_1535_, 5);
v___x_1593_ = 0;
v___x_1594_ = l_Lean_SourceInfo_fromRef(v_a_1590_, v___x_1593_);
lean_dec(v_a_1590_);
if (lean_obj_tag(v_quotContext_x3f_1592_) == 0)
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1536_);
lean_dec_ref(v___x_1729_);
goto v___jp_1595_;
}
else
{
goto v___jp_1595_;
}
v___jp_1595_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v_fst_1599_; lean_object* v_snd_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1728_; 
v___x_1596_ = lean_unsigned_to_nat(4u);
v___x_1597_ = l_Lean_Syntax_getArg(v_stx_1534_, v___x_1596_);
v___x_1598_ = l_Lean_Elab_expandDeclSig(v___x_1597_);
lean_dec(v___x_1597_);
v_fst_1599_ = lean_ctor_get(v___x_1598_, 0);
v_snd_1600_ = lean_ctor_get(v___x_1598_, 1);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1602_ = v___x_1598_;
v_isShared_1603_ = v_isSharedCheck_1728_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_snd_1600_);
lean_inc(v_fst_1599_);
lean_dec(v___x_1598_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1728_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1604_ = ((lean_object*)(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21_));
v___x_1605_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2));
v___x_1606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0));
v___x_1607_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4));
lean_inc(v___x_1594_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 2);
lean_ctor_set(v___x_1602_, 1, v___x_1606_);
lean_ctor_set(v___x_1602_, 0, v___x_1594_);
v___x_1609_ = v___x_1602_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v___x_1606_);
v___x_1609_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1610_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1611_ = l_Nat_reprFast(v_a_1588_);
v___x_1612_ = lean_box(2);
v___x_1613_ = l_Lean_Syntax_mkNumLit(v___x_1611_, v___x_1612_);
lean_inc(v___x_1594_);
v___x_1614_ = l_Lean_Syntax_node1(v___x_1594_, v___x_1610_, v___x_1613_);
v___x_1615_ = l_Lean_Syntax_node2(v___x_1594_, v___x_1607_, v___x_1609_, v___x_1614_);
v___x_1616_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1));
v___x_1617_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v___x_1615_);
v___x_1618_ = lean_unbox(v_a_1561_);
lean_dec(v_a_1561_);
lean_ctor_set_uint8(v___x_1617_, sizeof(void*)*2, v___x_1618_);
v___x_1619_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_1533_, v___x_1617_);
v___x_1620_ = lean_unsigned_to_nat(3u);
v___x_1621_ = l_Lean_Syntax_getArg(v_stx_1534_, v___x_1620_);
v___x_1622_ = l_Lean_Syntax_getOptional_x3f(v___x_1621_);
lean_dec(v___x_1621_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = l_Lean_Syntax_getArgs(v_fst_1599_);
lean_inc(v_snd_1600_);
v___x_1624_ = l_Lean_Elab_Command_mkInstanceName(v___x_1623_, v_snd_1600_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v_scopes_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v_opts_1632_; uint8_t v_hasTrace_1633_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1626_ = l_Lean_inheritedTraceOptions;
v___x_1627_ = lean_st_ref_get(v___x_1626_);
v___x_1628_ = lean_st_ref_get(v_a_1536_);
v_scopes_1629_ = lean_ctor_get(v___x_1628_, 2);
lean_inc(v_scopes_1629_);
lean_dec(v___x_1628_);
v___x_1630_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1631_ = l_List_head_x21___redArg(v___x_1630_, v_scopes_1629_);
lean_dec(v_scopes_1629_);
v_opts_1632_ = lean_ctor_get(v___x_1631_, 1);
lean_inc_ref(v_opts_1632_);
lean_dec(v___x_1631_);
v_hasTrace_1633_ = lean_ctor_get_uint8(v_opts_1632_, sizeof(void*)*1);
if (v_hasTrace_1633_ == 0)
{
lean_dec_ref(v_opts_1632_);
lean_dec(v___x_1627_);
v___y_1564_ = v___x_1612_;
v___y_1565_ = v_a_1625_;
v___y_1566_ = v___x_1610_;
v___y_1567_ = v_fst_1599_;
v___y_1568_ = v___x_1619_;
v___y_1569_ = v_snd_1600_;
v___y_1570_ = v___x_1604_;
v___y_1571_ = v___x_1605_;
goto v___jp_1563_;
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1635_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__7, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7);
v___x_1636_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1627_, v_opts_1632_, v___x_1635_);
lean_dec_ref(v_opts_1632_);
lean_dec(v___x_1627_);
if (v___x_1636_ == 0)
{
v___y_1564_ = v___x_1612_;
v___y_1565_ = v_a_1625_;
v___y_1566_ = v___x_1610_;
v___y_1567_ = v_fst_1599_;
v___y_1568_ = v___x_1619_;
v___y_1569_ = v_snd_1600_;
v___y_1570_ = v___x_1604_;
v___y_1571_ = v___x_1605_;
goto v___jp_1563_;
}
else
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Elab_Command_getScope___redArg(v_a_1536_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v_currNamespace_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v_currNamespace_1639_ = lean_ctor_get(v_a_1638_, 2);
lean_inc(v_currNamespace_1639_);
lean_dec(v_a_1638_);
v___x_1640_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__9, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
lean_inc(v_a_1625_);
v___x_1641_ = l_Lean_Name_append(v_currNamespace_1639_, v_a_1625_);
v___x_1642_ = l_Lean_MessageData_ofName(v___x_1641_);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1640_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_1634_, v___x_1643_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_dec_ref_known(v___x_1644_, 1);
v___y_1564_ = v___x_1612_;
v___y_1565_ = v_a_1625_;
v___y_1566_ = v___x_1610_;
v___y_1567_ = v_fst_1599_;
v___y_1568_ = v___x_1619_;
v___y_1569_ = v_snd_1600_;
v___y_1570_ = v___x_1604_;
v___y_1571_ = v___x_1605_;
goto v___jp_1563_;
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v_a_1625_);
lean_dec_ref(v___x_1619_);
lean_dec(v_snd_1600_);
lean_dec(v_fst_1599_);
lean_dec(v_stx_1534_);
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_a_1625_);
lean_dec_ref(v___x_1619_);
lean_dec(v_snd_1600_);
lean_dec(v_fst_1599_);
lean_dec(v_stx_1534_);
v_a_1653_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1637_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1637_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v___x_1619_);
lean_dec(v_snd_1600_);
lean_dec(v_fst_1599_);
lean_dec(v_stx_1534_);
v_a_1661_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1624_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1624_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_val_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v_scopes_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_opts_1676_; uint8_t v_hasTrace_1677_; 
v_val_1669_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_val_1669_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1670_ = l_Lean_inheritedTraceOptions;
v___x_1671_ = lean_st_ref_get(v___x_1670_);
v___x_1672_ = lean_st_ref_get(v_a_1536_);
v_scopes_1673_ = lean_ctor_get(v___x_1672_, 2);
lean_inc(v_scopes_1673_);
lean_dec(v___x_1672_);
v___x_1674_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1675_ = l_List_head_x21___redArg(v___x_1674_, v_scopes_1673_);
lean_dec(v_scopes_1673_);
v_opts_1676_ = lean_ctor_get(v___x_1675_, 1);
lean_inc_ref(v_opts_1676_);
lean_dec(v___x_1675_);
v_hasTrace_1677_ = lean_ctor_get_uint8(v_opts_1676_, sizeof(void*)*1);
if (v_hasTrace_1677_ == 0)
{
lean_dec_ref(v_opts_1676_);
lean_dec(v___x_1671_);
v___y_1540_ = v___x_1612_;
v___y_1541_ = v___x_1610_;
v___y_1542_ = v_fst_1599_;
v___y_1543_ = v___x_1619_;
v___y_1544_ = v_snd_1600_;
v_declId_1545_ = v_val_1669_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1678_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1679_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__7, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7);
v___x_1680_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1671_, v_opts_1676_, v___x_1679_);
lean_dec_ref(v_opts_1676_);
lean_dec(v___x_1671_);
if (v___x_1680_ == 0)
{
v___y_1540_ = v___x_1612_;
v___y_1541_ = v___x_1610_;
v___y_1542_ = v_fst_1599_;
v___y_1543_ = v___x_1619_;
v___y_1544_ = v_snd_1600_;
v_declId_1545_ = v_val_1669_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = l_Lean_Syntax_getArgs(v_fst_1599_);
lean_inc(v_snd_1600_);
v___x_1682_ = l_Lean_Elab_Command_mkInstanceName(v___x_1681_, v_snd_1600_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v_scopes_1686_; lean_object* v___x_1687_; lean_object* v_opts_1688_; uint8_t v_hasTrace_1689_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1682_, 1);
v___x_1684_ = lean_st_ref_get(v___x_1670_);
v___x_1685_ = lean_st_ref_get(v_a_1536_);
v_scopes_1686_ = lean_ctor_get(v___x_1685_, 2);
lean_inc(v_scopes_1686_);
lean_dec(v___x_1685_);
v___x_1687_ = l_List_head_x21___redArg(v___x_1674_, v_scopes_1686_);
lean_dec(v_scopes_1686_);
v_opts_1688_ = lean_ctor_get(v___x_1687_, 1);
lean_inc_ref(v_opts_1688_);
lean_dec(v___x_1687_);
v_hasTrace_1689_ = lean_ctor_get_uint8(v_opts_1688_, sizeof(void*)*1);
if (v_hasTrace_1689_ == 0)
{
lean_dec_ref(v_opts_1688_);
lean_dec(v___x_1684_);
lean_dec(v_a_1683_);
v___y_1540_ = v___x_1612_;
v___y_1541_ = v___x_1610_;
v___y_1542_ = v_fst_1599_;
v___y_1543_ = v___x_1619_;
v___y_1544_ = v_snd_1600_;
v_declId_1545_ = v_val_1669_;
goto v___jp_1539_;
}
else
{
uint8_t v___x_1690_; 
v___x_1690_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1684_, v_opts_1688_, v___x_1679_);
lean_dec_ref(v_opts_1688_);
lean_dec(v___x_1684_);
if (v___x_1690_ == 0)
{
lean_dec(v_a_1683_);
v___y_1540_ = v___x_1612_;
v___y_1541_ = v___x_1610_;
v___y_1542_ = v_fst_1599_;
v___y_1543_ = v___x_1619_;
v___y_1544_ = v_snd_1600_;
v_declId_1545_ = v_val_1669_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_Elab_Command_getScope___redArg(v_a_1536_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v_currNamespace_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v_currNamespace_1693_ = lean_ctor_get(v_a_1692_, 2);
lean_inc(v_currNamespace_1693_);
lean_dec(v_a_1692_);
v___x_1694_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__9, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
v___x_1695_ = l_Lean_Name_append(v_currNamespace_1693_, v_a_1683_);
v___x_1696_ = l_Lean_MessageData_ofName(v___x_1695_);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1694_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__11, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__11_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
lean_inc(v_val_1669_);
v___x_1700_ = l_Lean_MessageData_ofSyntax(v_val_1669_);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_1678_, v___x_1701_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_dec_ref_known(v___x_1702_, 1);
v___y_1540_ = v___x_1612_;
v___y_1541_ = v___x_1610_;
v___y_1542_ = v_fst_1599_;
v___y_1543_ = v___x_1619_;
v___y_1544_ = v_snd_1600_;
v_declId_1545_ = v_val_1669_;
goto v___jp_1539_;
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_val_1669_);
lean_dec_ref(v___x_1619_);
lean_dec(v_snd_1600_);
lean_dec(v_fst_1599_);
lean_dec(v_stx_1534_);
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1702_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v_a_1683_);
lean_dec(v_val_1669_);
lean_dec_ref(v___x_1619_);
lean_dec(v_snd_1600_);
lean_dec(v_fst_1599_);
lean_dec(v_stx_1534_);
v_a_1711_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1691_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1691_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_val_1669_);
lean_dec_ref(v___x_1619_);
lean_dec(v_snd_1600_);
lean_dec(v_fst_1599_);
lean_dec(v_stx_1534_);
v_a_1719_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1682_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1682_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
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
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1588_);
lean_dec(v_a_1561_);
lean_dec(v_stx_1534_);
lean_dec_ref(v_modifiers_1533_);
v_a_1730_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1591_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1591_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec(v_a_1588_);
lean_dec(v_a_1561_);
lean_dec(v_stx_1534_);
lean_dec_ref(v_modifiers_1533_);
v_a_1738_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1589_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1589_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_a_1561_);
lean_dec(v_stx_1534_);
lean_dec_ref(v_modifiers_1533_);
v_a_1746_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1587_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1587_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
v___jp_1563_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0));
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__1));
lean_inc_ref(v___y_1571_);
lean_inc_ref(v___y_1570_);
v___x_1574_ = l_Lean_Name_mkStr4(v___y_1570_, v___y_1571_, v___x_1572_, v___x_1573_);
v___x_1575_ = lean_unsigned_to_nat(1u);
v___x_1576_ = l_Lean_Syntax_getArg(v_stx_1534_, v___x_1575_);
v___x_1577_ = 1;
v___x_1578_ = l_Lean_mkIdentFrom(v___x_1576_, v___y_1565_, v___x_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = ((lean_object*)(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0));
lean_inc(v___y_1566_);
lean_inc_n(v___y_1564_, 2);
v___x_1580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1580_, 0, v___y_1564_);
lean_ctor_set(v___x_1580_, 1, v___y_1566_);
lean_ctor_set(v___x_1580_, 2, v___x_1579_);
v___x_1581_ = lean_mk_empty_array_with_capacity(v___x_1562_);
v___x_1582_ = lean_array_push(v___x_1581_, v___x_1578_);
v___x_1583_ = lean_array_push(v___x_1582_, v___x_1580_);
v___x_1584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1584_, 0, v___y_1564_);
lean_ctor_set(v___x_1584_, 1, v___x_1574_);
lean_ctor_set(v___x_1584_, 2, v___x_1583_);
v___y_1540_ = v___y_1564_;
v___y_1541_ = v___y_1566_;
v___y_1542_ = v___y_1567_;
v___y_1543_ = v___y_1568_;
v___y_1544_ = v___y_1569_;
v_declId_1545_ = v___x_1584_;
goto v___jp_1539_;
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_stx_1534_);
lean_dec_ref(v_modifiers_1533_);
v_a_1754_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1560_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1560_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
v___jp_1539_:
{
lean_object* v_docString_x3f_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_docString_x3f_1546_ = lean_ctor_get(v___y_1543_, 1);
lean_inc(v_docString_x3f_1546_);
v___x_1547_ = 1;
v___x_1548_ = l_Lean_Syntax_getArgs(v_stx_1534_);
v___x_1549_ = lean_unsigned_to_nat(5u);
v___x_1550_ = l_Array_toSubarray___redArg(v___x_1548_, v___x_1538_, v___x_1549_);
v___x_1551_ = l_Subarray_copy___redArg(v___x_1550_);
v___x_1552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1552_, 0, v___y_1540_);
lean_ctor_set(v___x_1552_, 1, v___y_1541_);
lean_ctor_set(v___x_1552_, 2, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___y_1544_);
v___x_1554_ = l_Lean_Syntax_getArg(v_stx_1534_, v___x_1549_);
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1556_, 0, v_stx_1534_);
lean_ctor_set(v___x_1556_, 1, v___x_1552_);
lean_ctor_set(v___x_1556_, 2, v___y_1543_);
lean_ctor_set(v___x_1556_, 3, v_declId_1545_);
lean_ctor_set(v___x_1556_, 4, v___y_1542_);
lean_ctor_set(v___x_1556_, 5, v___x_1553_);
lean_ctor_set(v___x_1556_, 6, v___x_1554_);
lean_ctor_set(v___x_1556_, 7, v_docString_x3f_1546_);
lean_ctor_set(v___x_1556_, 8, v___x_1555_);
lean_ctor_set(v___x_1556_, 9, v___x_1555_);
lean_ctor_set_uint8(v___x_1556_, sizeof(void*)*10, v___x_1547_);
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object* v_modifiers_1762_, lean_object* v_stx_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_Elab_Command_mkDefViewOfInstance(v_modifiers_1762_, v_stx_1763_, v_a_1764_, v_a_1765_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(lean_object* v_00_u03b1_1768_, lean_object* v_x_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_1769_, v___y_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1773_, lean_object* v_x_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(v_00_u03b1_1773_, v_x_1774_, v___y_1775_, v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_x_1774_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(lean_object* v_00_u03b1_1778_, lean_object* v_ref_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_1779_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1784_, lean_object* v_ref_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(v_00_u03b1_1784_, v_ref_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(lean_object* v_00_u03b1_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(v_00_u03b1_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(lean_object* v_00_u03b1_1800_, lean_object* v_x_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v_x_1801_, v___y_1802_, v___y_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___boxed(lean_object* v_00_u03b1_1806_, lean_object* v_x_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(v_00_u03b1_1806_, v_x_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(lean_object* v_msgData_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_1812_, v___y_1814_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___boxed(lean_object* v_msgData_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(v_msgData_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(lean_object* v_as_1822_, lean_object* v_as_x27_1823_, lean_object* v_b_1824_, lean_object* v_a_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_1823_, v_b_1824_, v___y_1826_, v___y_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___boxed(lean_object* v_as_1830_, lean_object* v_as_x27_1831_, lean_object* v_b_1832_, lean_object* v_a_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(v_as_1830_, v_as_x27_1831_, v_b_1832_, v_a_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v_as_x27_1831_);
lean_dec(v_as_1830_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(lean_object* v_00_u03b1_1838_, lean_object* v_ref_1839_, lean_object* v_msg_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_1839_, v_msg_1840_, v___y_1841_, v___y_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1845_, lean_object* v_ref_1846_, lean_object* v_msg_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(v_00_u03b1_1845_, v_ref_1846_, v_msg_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v_ref_1846_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1852_, lean_object* v_m_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_1853_, v_a_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_1856_, lean_object* v_m_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(v_00_u03b2_1856_, v_m_1857_, v_a_1858_);
lean_dec(v_a_1858_);
lean_dec_ref(v_m_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(lean_object* v_00_u03b1_1860_, lean_object* v_msg_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1861_, v___y_1862_, v___y_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1866_, lean_object* v_msg_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(v_00_u03b1_1866_, v_msg_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1871_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_){
_start:
{
uint8_t v___x_1875_; 
v___x_1875_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_1873_, v_x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
uint8_t v_res_1879_; lean_object* v_r_1880_; 
v_res_1879_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_1876_, v_x_1877_, v_x_1878_);
lean_dec_ref(v_x_1878_);
lean_dec_ref(v_x_1877_);
v_r_1880_ = lean_box(v_res_1879_);
return v_r_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1881_, lean_object* v_m_1882_, lean_object* v_query_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_m_1882_, v_query_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1885_, lean_object* v_m_1886_, lean_object* v_query_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(v_00_u03b2_1885_, v_m_1886_, v_query_1887_);
lean_dec(v_query_1887_);
lean_dec_ref(v_m_1886_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(lean_object* v_msgData_1889_, lean_object* v_macroStack_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_1889_, v_macroStack_1890_, v___y_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___boxed(lean_object* v_msgData_1895_, lean_object* v_macroStack_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(v_msgData_1895_, v_macroStack_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1900_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_1901_, lean_object* v_x_1902_, size_t v_x_1903_, lean_object* v_x_1904_){
_start:
{
uint8_t v___x_1905_; 
v___x_1905_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_1902_, v_x_1903_, v_x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_, lean_object* v_x_1909_){
_start:
{
size_t v_x_19038__boxed_1910_; uint8_t v_res_1911_; lean_object* v_r_1912_; 
v_x_19038__boxed_1910_ = lean_unbox_usize(v_x_1908_);
lean_dec(v_x_1908_);
v_res_1911_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_1906_, v_x_1907_, v_x_19038__boxed_1910_, v_x_1909_);
lean_dec_ref(v_x_1909_);
lean_dec_ref(v_x_1907_);
v_r_1912_ = lean_box(v_res_1911_);
return v_r_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16(lean_object* v_00_u03b2_1913_, lean_object* v_m_1914_, lean_object* v_query_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16___redArg(v_m_1914_, v_query_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16___boxed(lean_object* v_00_u03b2_1917_, lean_object* v_m_1918_, lean_object* v_query_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16(v_00_u03b2_1917_, v_m_1918_, v_query_1919_);
lean_dec(v_query_1919_);
lean_dec_ref(v_m_1918_);
return v_res_1920_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(lean_object* v_00_u03b2_1921_, lean_object* v_keys_1922_, lean_object* v_vals_1923_, lean_object* v_heq_1924_, lean_object* v_i_1925_, lean_object* v_k_1926_){
_start:
{
uint8_t v___x_1927_; 
v___x_1927_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_1922_, v_i_1925_, v_k_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___boxed(lean_object* v_00_u03b2_1928_, lean_object* v_keys_1929_, lean_object* v_vals_1930_, lean_object* v_heq_1931_, lean_object* v_i_1932_, lean_object* v_k_1933_){
_start:
{
uint8_t v_res_1934_; lean_object* v_r_1935_; 
v_res_1934_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(v_00_u03b2_1928_, v_keys_1929_, v_vals_1930_, v_heq_1931_, v_i_1932_, v_k_1933_);
lean_dec_ref(v_k_1933_);
lean_dec_ref(v_vals_1930_);
lean_dec_ref(v_keys_1929_);
v_r_1935_ = lean_box(v_res_1934_);
return v_r_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19(lean_object* v_00_u03b2_1936_, lean_object* v_m_1937_, lean_object* v_query_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_, lean_object* v_x_1941_, lean_object* v_x_1942_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19___redArg(v_m_1937_, v_query_1938_, v_x_1939_, v_x_1940_, v_x_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19___boxed(lean_object* v_00_u03b2_1944_, lean_object* v_m_1945_, lean_object* v_query_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11_spec__16_spec__19(v_00_u03b2_1944_, v_m_1945_, v_query_1946_, v_x_1947_, v_x_1948_, v_x_1949_, v_x_1950_);
lean_dec(v_query_1946_);
lean_dec_ref(v_m_1945_);
return v_res_1951_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6(void){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Array_mkArray0(lean_box(0));
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque(lean_object* v_modifiers_1976_, lean_object* v_stx_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_fst_1984_; lean_object* v_snd_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2115_; 
v___x_1981_ = lean_unsigned_to_nat(2u);
v___x_1982_ = l_Lean_Syntax_getArg(v_stx_1977_, v___x_1981_);
v___x_1983_ = l_Lean_Elab_expandDeclSig(v___x_1982_);
lean_dec(v___x_1982_);
v_fst_1984_ = lean_ctor_get(v___x_1983_, 0);
v_snd_1985_ = lean_ctor_get(v___x_1983_, 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_1987_ = v___x_1983_;
v_isShared_1988_ = v_isSharedCheck_2115_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_snd_1985_);
lean_inc(v_fst_1984_);
lean_dec(v___x_1983_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2115_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v_val_1990_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v_val_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = lean_unsigned_to_nat(3u);
v___x_2049_ = l_Lean_Syntax_getArg(v_stx_1977_, v___x_2048_);
v___x_2050_ = l_Lean_Syntax_getOptional_x3f(v___x_2049_);
lean_dec(v___x_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
uint8_t v_isUnsafe_2051_; 
v_isUnsafe_2051_ = lean_ctor_get_uint8(v_modifiers_1976_, sizeof(void*)*3 + 4);
if (v_isUnsafe_2051_ == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Elab_Command_getRef___redArg(v_a_1978_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2054_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
v___x_2054_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1978_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_quotContext_x3f_2055_; lean_object* v___x_2056_; 
lean_dec_ref_known(v___x_2054_, 1);
v_quotContext_x3f_2055_ = lean_ctor_get(v_a_1978_, 5);
v___x_2056_ = l_Lean_SourceInfo_fromRef(v_a_2053_, v_isUnsafe_2051_);
lean_dec(v_a_2053_);
if (lean_obj_tag(v_quotContext_x3f_2055_) == 0)
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1979_);
lean_dec_ref(v___x_2065_);
goto v___jp_2057_;
}
else
{
goto v___jp_2057_;
}
v___jp_2057_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2058_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9));
v___x_2059_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10));
lean_inc_n(v___x_2056_, 2);
v___x_2060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2056_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_2062_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6, &l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once, _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6);
v___x_2063_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2056_);
lean_ctor_set(v___x_2063_, 1, v___x_2061_);
lean_ctor_set(v___x_2063_, 2, v___x_2062_);
v___x_2064_ = l_Lean_Syntax_node2(v___x_2056_, v___x_2058_, v___x_2060_, v___x_2063_);
v_val_2022_ = v___x_2064_;
v___y_2023_ = v_a_1978_;
v___y_2024_ = v_a_1979_;
goto v___jp_2021_;
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_a_2053_);
lean_del_object(v___x_1987_);
lean_dec(v_snd_1985_);
lean_dec(v_fst_1984_);
lean_dec(v_stx_1977_);
lean_dec_ref(v_modifiers_1976_);
v_a_2066_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2054_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2054_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_del_object(v___x_1987_);
lean_dec(v_snd_1985_);
lean_dec(v_fst_1984_);
lean_dec(v_stx_1977_);
lean_dec_ref(v_modifiers_1976_);
v_a_2074_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2052_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2052_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_Elab_Command_getRef___redArg(v_a_1978_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2084_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2084_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1978_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_quotContext_x3f_2085_; uint8_t v___x_2086_; lean_object* v___x_2087_; 
lean_dec_ref_known(v___x_2084_, 1);
v_quotContext_x3f_2085_ = lean_ctor_get(v_a_1978_, 5);
v___x_2086_ = 0;
v___x_2087_ = l_Lean_SourceInfo_fromRef(v_a_2083_, v___x_2086_);
lean_dec(v_a_2083_);
if (lean_obj_tag(v_quotContext_x3f_2085_) == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1979_);
lean_dec_ref(v___x_2097_);
goto v___jp_2088_;
}
else
{
goto v___jp_2088_;
}
v___jp_2088_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2089_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9));
v___x_2090_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10));
lean_inc_n(v___x_2087_, 3);
v___x_2091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2087_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_2093_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11));
v___x_2094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2087_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = l_Lean_Syntax_node1(v___x_2087_, v___x_2092_, v___x_2094_);
v___x_2096_ = l_Lean_Syntax_node2(v___x_2087_, v___x_2089_, v___x_2091_, v___x_2095_);
v_val_2022_ = v___x_2096_;
v___y_2023_ = v_a_1978_;
v___y_2024_ = v_a_1979_;
goto v___jp_2021_;
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v_a_2083_);
lean_del_object(v___x_1987_);
lean_dec(v_snd_1985_);
lean_dec(v_fst_1984_);
lean_dec(v_stx_1977_);
lean_dec_ref(v_modifiers_1976_);
v_a_2098_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2084_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2084_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_del_object(v___x_1987_);
lean_dec(v_snd_1985_);
lean_dec(v_fst_1984_);
lean_dec(v_stx_1977_);
lean_dec_ref(v_modifiers_1976_);
v_a_2106_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2082_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2082_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
else
{
lean_object* v_val_2114_; 
lean_del_object(v___x_1987_);
v_val_2114_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_val_2114_);
lean_dec_ref_known(v___x_2050_, 1);
v_val_1990_ = v_val_2114_;
goto v___jp_1989_;
}
v___jp_1989_:
{
lean_object* v_docString_x3f_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v_docString_x3f_1991_ = lean_ctor_get(v_modifiers_1976_, 1);
lean_inc(v_docString_x3f_1991_);
v___x_1992_ = 4;
v___x_1993_ = l_Lean_Syntax_getArgs(v_stx_1977_);
v___x_1994_ = lean_unsigned_to_nat(3u);
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_1996_ = l_Array_toSubarray___redArg(v___x_1993_, v___x_1995_, v___x_1994_);
v___x_1997_ = l_Subarray_copy___redArg(v___x_1996_);
v___x_1998_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1999_ = lean_box(2);
v___x_2000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set(v___x_2000_, 1, v___x_1998_);
lean_ctor_set(v___x_2000_, 2, v___x_1997_);
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = l_Lean_Syntax_getArg(v_stx_1977_, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_snd_1985_);
v___x_2004_ = lean_box(0);
v___x_2005_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2005_, 0, v_stx_1977_);
lean_ctor_set(v___x_2005_, 1, v___x_2000_);
lean_ctor_set(v___x_2005_, 2, v_modifiers_1976_);
lean_ctor_set(v___x_2005_, 3, v___x_2002_);
lean_ctor_set(v___x_2005_, 4, v_fst_1984_);
lean_ctor_set(v___x_2005_, 5, v___x_2003_);
lean_ctor_set(v___x_2005_, 6, v_val_1990_);
lean_ctor_set(v___x_2005_, 7, v_docString_x3f_1991_);
lean_ctor_set(v___x_2005_, 8, v___x_2004_);
lean_ctor_set(v___x_2005_, 9, v___x_2004_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*10, v___x_1992_);
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
return v___x_2006_;
}
v___jp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2010_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1));
v___x_2011_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2));
lean_inc(v___y_2008_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 2);
lean_ctor_set(v___x_1987_, 1, v___x_2011_);
lean_ctor_set(v___x_1987_, 0, v___y_2008_);
v___x_2013_ = v___x_1987_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___y_2008_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2014_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5));
v___x_2015_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_2016_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6, &l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once, _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6);
lean_inc_n(v___y_2008_, 2);
v___x_2017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2017_, 0, v___y_2008_);
lean_ctor_set(v___x_2017_, 1, v___x_2015_);
lean_ctor_set(v___x_2017_, 2, v___x_2016_);
lean_inc_ref_n(v___x_2017_, 2);
v___x_2018_ = l_Lean_Syntax_node2(v___y_2008_, v___x_2014_, v___x_2017_, v___x_2017_);
v___x_2019_ = l_Lean_Syntax_node4(v___y_2008_, v___x_2010_, v___x_2013_, v___y_2009_, v___x_2018_, v___x_2017_);
v_val_1990_ = v___x_2019_;
goto v___jp_1989_;
}
}
v___jp_2021_:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Elab_Command_getRef___redArg(v___y_2023_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2023_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_quotContext_x3f_2028_; uint8_t v___x_2029_; lean_object* v___x_2030_; 
lean_dec_ref_known(v___x_2027_, 1);
v_quotContext_x3f_2028_ = lean_ctor_get(v___y_2023_, 5);
v___x_2029_ = 0;
v___x_2030_ = l_Lean_SourceInfo_fromRef(v_a_2026_, v___x_2029_);
lean_dec(v_a_2026_);
if (lean_obj_tag(v_quotContext_x3f_2028_) == 0)
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_2024_);
lean_dec_ref(v___x_2031_);
v___y_2008_ = v___x_2030_;
v___y_2009_ = v_val_2022_;
goto v___jp_2007_;
}
else
{
v___y_2008_ = v___x_2030_;
v___y_2009_ = v_val_2022_;
goto v___jp_2007_;
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_a_2026_);
lean_dec(v_val_2022_);
lean_del_object(v___x_1987_);
lean_dec(v_snd_1985_);
lean_dec(v_fst_1984_);
lean_dec(v_stx_1977_);
lean_dec_ref(v_modifiers_1976_);
v_a_2032_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2027_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2027_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_val_2022_);
lean_del_object(v___x_1987_);
lean_dec(v_snd_1985_);
lean_dec(v_fst_1984_);
lean_dec(v_stx_1977_);
lean_dec_ref(v_modifiers_1976_);
v_a_2040_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2025_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2025_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___boxed(lean_object* v_modifiers_2116_, lean_object* v_stx_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_Elab_Command_mkDefViewOfOpaque(v_modifiers_2116_, v_stx_2117_, v_a_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object* v_modifiers_2134_, lean_object* v_stx_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_fst_2139_; lean_object* v_snd_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v_docString_x3f_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; lean_object* v_id_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2136_ = lean_unsigned_to_nat(1u);
v___x_2137_ = l_Lean_Syntax_getArg(v_stx_2135_, v___x_2136_);
v___x_2138_ = l_Lean_Elab_expandOptDeclSig(v___x_2137_);
lean_dec(v___x_2137_);
v_fst_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_fst_2139_);
v_snd_2140_ = lean_ctor_get(v___x_2138_, 1);
lean_inc(v_snd_2140_);
lean_dec_ref(v___x_2138_);
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_2143_ = lean_box(2);
v___x_2144_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__0));
v_docString_x3f_2145_ = lean_ctor_get(v_modifiers_2134_, 1);
lean_inc(v_docString_x3f_2145_);
v___x_2146_ = l_Lean_Syntax_getArg(v_stx_2135_, v___x_2141_);
v___x_2147_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__2));
v___x_2148_ = 1;
v_id_2149_ = l_Lean_mkIdentFrom(v___x_2146_, v___x_2147_, v___x_2148_);
lean_dec(v___x_2146_);
v___x_2150_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__3));
v___x_2151_ = lean_unsigned_to_nat(2u);
v___x_2152_ = lean_mk_empty_array_with_capacity(v___x_2151_);
v___x_2153_ = lean_array_push(v___x_2152_, v_id_2149_);
v___x_2154_ = lean_array_push(v___x_2153_, v___x_2144_);
v___x_2155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2143_);
lean_ctor_set(v___x_2155_, 1, v___x_2150_);
lean_ctor_set(v___x_2155_, 2, v___x_2154_);
v___x_2156_ = 3;
v___x_2157_ = l_Lean_Syntax_getArgs(v_stx_2135_);
v___x_2158_ = l_Array_toSubarray___redArg(v___x_2157_, v___x_2141_, v___x_2151_);
v___x_2159_ = l_Subarray_copy___redArg(v___x_2158_);
v___x_2160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2143_);
lean_ctor_set(v___x_2160_, 1, v___x_2142_);
lean_ctor_set(v___x_2160_, 2, v___x_2159_);
v___x_2161_ = l_Lean_Syntax_getArg(v_stx_2135_, v___x_2151_);
v___x_2162_ = lean_box(0);
v___x_2163_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2163_, 0, v_stx_2135_);
lean_ctor_set(v___x_2163_, 1, v___x_2160_);
lean_ctor_set(v___x_2163_, 2, v_modifiers_2134_);
lean_ctor_set(v___x_2163_, 3, v___x_2155_);
lean_ctor_set(v___x_2163_, 4, v_fst_2139_);
lean_ctor_set(v___x_2163_, 5, v_snd_2140_);
lean_ctor_set(v___x_2163_, 6, v___x_2161_);
lean_ctor_set(v___x_2163_, 7, v_docString_x3f_2145_);
lean_ctor_set(v___x_2163_, 8, v___x_2162_);
lean_ctor_set(v___x_2163_, 9, v___x_2162_);
lean_ctor_set_uint8(v___x_2163_, sizeof(void*)*10, v___x_2156_);
return v___x_2163_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_isDefLike(lean_object* v_stx_2199_){
_start:
{
lean_object* v_declKind_2200_; uint8_t v___y_2202_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v_declKind_2200_ = l_Lean_Syntax_getKind(v_stx_2199_);
v___x_2211_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__8));
v___x_2212_ = lean_name_eq(v_declKind_2200_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__10));
v___x_2214_ = lean_name_eq(v_declKind_2200_, v___x_2213_);
v___y_2202_ = v___x_2214_;
goto v___jp_2201_;
}
else
{
v___y_2202_ = v___x_2212_;
goto v___jp_2201_;
}
v___jp_2201_:
{
if (v___y_2202_ == 0)
{
lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2204_ = lean_name_eq(v_declKind_2200_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__3));
v___x_2206_ = lean_name_eq(v_declKind_2200_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__4));
v___x_2208_ = lean_name_eq(v_declKind_2200_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2210_ = lean_name_eq(v_declKind_2200_, v___x_2209_);
lean_dec(v_declKind_2200_);
return v___x_2210_;
}
else
{
lean_dec(v_declKind_2200_);
return v___x_2208_;
}
}
else
{
lean_dec(v_declKind_2200_);
return v___x_2206_;
}
}
else
{
lean_dec(v_declKind_2200_);
return v___x_2204_;
}
}
else
{
lean_dec(v_declKind_2200_);
return v___y_2202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object* v_stx_2215_){
_start:
{
uint8_t v_res_2216_; lean_object* v_r_2217_; 
v_res_2216_ = l_Lean_Elab_Command_isDefLike(v_stx_2215_);
v_r_2217_ = lean_box(v_res_2216_);
return v_r_2217_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefView___closed__1(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = ((lean_object*)(l_Lean_Elab_Command_mkDefView___closed__0));
v___x_2220_ = l_Lean_stringToMessageData(v___x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView(lean_object* v_modifiers_2221_, lean_object* v_stx_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_Elab_Command_getScope___redArg(v_a_2224_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2294_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2294_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2294_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_stx_2231_; lean_object* v_docString_x3f_2232_; uint8_t v_visibility_2233_; uint8_t v_isProtected_2234_; uint8_t v_computeKind_2235_; uint8_t v_recKind_2236_; uint8_t v_isUnsafe_2237_; lean_object* v_attrs_2238_; lean_object* v_declKind_2239_; lean_object* v___y_2241_; uint8_t v___y_2275_; uint8_t v___x_2291_; uint8_t v___x_2292_; 
v_stx_2231_ = lean_ctor_get(v_modifiers_2221_, 0);
v_docString_x3f_2232_ = lean_ctor_get(v_modifiers_2221_, 1);
v_visibility_2233_ = lean_ctor_get_uint8(v_modifiers_2221_, sizeof(void*)*3);
v_isProtected_2234_ = lean_ctor_get_uint8(v_modifiers_2221_, sizeof(void*)*3 + 1);
v_computeKind_2235_ = lean_ctor_get_uint8(v_modifiers_2221_, sizeof(void*)*3 + 2);
v_recKind_2236_ = lean_ctor_get_uint8(v_modifiers_2221_, sizeof(void*)*3 + 3);
v_isUnsafe_2237_ = lean_ctor_get_uint8(v_modifiers_2221_, sizeof(void*)*3 + 4);
v_attrs_2238_ = lean_ctor_get(v_modifiers_2221_, 2);
lean_inc(v_stx_2222_);
v_declKind_2239_ = l_Lean_Syntax_getKind(v_stx_2222_);
v___x_2291_ = 0;
v___x_2292_ = l_Lean_Elab_instBEqComputeKind_beq(v_computeKind_2235_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_dec(v_a_2227_);
v___y_2275_ = v___x_2292_;
goto v___jp_2274_;
}
else
{
uint8_t v_isMeta_2293_; 
v_isMeta_2293_ = lean_ctor_get_uint8(v_a_2227_, sizeof(void*)*10 + 2);
lean_dec(v_a_2227_);
v___y_2275_ = v_isMeta_2293_;
goto v___jp_2274_;
}
v___jp_2240_:
{
lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__8));
v___x_2243_ = lean_name_eq(v_declKind_2239_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__10));
v___x_2245_ = lean_name_eq(v_declKind_2239_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; uint8_t v___x_2247_; 
v___x_2246_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2247_ = lean_name_eq(v_declKind_2239_, v___x_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2248_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__3));
v___x_2249_ = lean_name_eq(v_declKind_2239_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; uint8_t v___x_2251_; 
v___x_2250_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__4));
v___x_2251_ = lean_name_eq(v_declKind_2239_, v___x_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2252_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2253_ = lean_name_eq(v_declKind_2239_, v___x_2252_);
lean_dec(v_declKind_2239_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec_ref(v___y_2241_);
lean_del_object(v___x_2229_);
lean_dec(v_stx_2222_);
v___x_2254_ = lean_obj_once(&l_Lean_Elab_Command_mkDefView___closed__1, &l_Lean_Elab_Command_mkDefView___closed__1_once, _init_l_Lean_Elab_Command_mkDefView___closed__1);
v___x_2255_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v___x_2254_, v_a_2223_, v_a_2224_);
return v___x_2255_;
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = l_Lean_Elab_Command_mkDefViewOfExample(v___y_2241_, v_stx_2222_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2256_);
v___x_2258_ = v___x_2229_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
else
{
lean_object* v___x_2260_; 
lean_dec(v_declKind_2239_);
lean_del_object(v___x_2229_);
v___x_2260_ = l_Lean_Elab_Command_mkDefViewOfInstance(v___y_2241_, v_stx_2222_, v_a_2223_, v_a_2224_);
return v___x_2260_;
}
}
else
{
lean_object* v___x_2261_; 
lean_dec(v_declKind_2239_);
lean_del_object(v___x_2229_);
v___x_2261_ = l_Lean_Elab_Command_mkDefViewOfOpaque(v___y_2241_, v_stx_2222_, v_a_2223_, v_a_2224_);
return v___x_2261_;
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
lean_dec(v_declKind_2239_);
v___x_2262_ = l_Lean_Elab_Command_mkDefViewOfTheorem(v___y_2241_, v_stx_2222_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2262_);
v___x_2264_ = v___x_2229_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_dec(v_declKind_2239_);
v___x_2266_ = l_Lean_Elab_Command_mkDefViewOfDef(v___y_2241_, v_stx_2222_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2266_);
v___x_2268_ = v___x_2229_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
lean_dec(v_declKind_2239_);
v___x_2270_ = l_Lean_Elab_Command_mkDefViewOfAbbrev(v___y_2241_, v_stx_2222_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2270_);
v___x_2272_ = v___x_2229_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
v___jp_2274_:
{
if (v___y_2275_ == 0)
{
v___y_2241_ = v_modifiers_2221_;
goto v___jp_2240_;
}
else
{
lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2276_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2277_ = lean_name_eq(v_declKind_2239_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2278_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2279_ = lean_name_eq(v_declKind_2239_, v___x_2278_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2287_; 
lean_inc_ref(v_attrs_2238_);
lean_inc(v_docString_x3f_2232_);
lean_inc(v_stx_2231_);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_modifiers_2221_);
if (v_isSharedCheck_2287_ == 0)
{
lean_object* v_unused_2288_; lean_object* v_unused_2289_; lean_object* v_unused_2290_; 
v_unused_2288_ = lean_ctor_get(v_modifiers_2221_, 2);
lean_dec(v_unused_2288_);
v_unused_2289_ = lean_ctor_get(v_modifiers_2221_, 1);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v_modifiers_2221_, 0);
lean_dec(v_unused_2290_);
v___x_2281_ = v_modifiers_2221_;
v_isShared_2282_ = v_isSharedCheck_2287_;
goto v_resetjp_2280_;
}
else
{
lean_dec(v_modifiers_2221_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2287_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
uint8_t v___x_2283_; lean_object* v___x_2285_; 
v___x_2283_ = 1;
if (v_isShared_2282_ == 0)
{
v___x_2285_ = v___x_2281_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_stx_2231_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_docString_x3f_2232_);
lean_ctor_set(v_reuseFailAlloc_2286_, 2, v_attrs_2238_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*3, v_visibility_2233_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*3 + 1, v_isProtected_2234_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*3 + 3, v_recKind_2236_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*3 + 4, v_isUnsafe_2237_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*3 + 2, v___x_2283_);
v___y_2241_ = v___x_2285_;
goto v___jp_2240_;
}
}
}
else
{
v___y_2241_ = v_modifiers_2221_;
goto v___jp_2240_;
}
}
else
{
v___y_2241_ = v_modifiers_2221_;
goto v___jp_2240_;
}
}
}
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v_stx_2222_);
lean_dec_ref(v_modifiers_2221_);
v_a_2295_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2226_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2226_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object* v_modifiers_2303_, lean_object* v_stx_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Elab_Command_mkDefView(v_modifiers_2303_, v_stx_2304_, v_a_2305_, v_a_2306_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2371_ = 0;
v___x_2372_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2373_ = l_Lean_registerTraceClass(v___x_2370_, v___x_2371_, v___x_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2____boxed(lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_();
return v_res_2375_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = lean_unsigned_to_nat(2390142386u);
v___x_2377_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2378_ = l_Lean_Name_num___override(v___x_2377_, v___x_2376_);
return v___x_2378_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2379_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2380_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2381_ = l_Lean_Name_str___override(v___x_2380_, v___x_2379_);
return v___x_2381_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2383_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2384_ = l_Lean_Name_str___override(v___x_2383_, v___x_2382_);
return v___x_2384_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = lean_unsigned_to_nat(2u);
v___x_2386_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2387_ = l_Lean_Name_num___override(v___x_2386_, v___x_2385_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2389_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_2390_ = 0;
v___x_2391_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2392_ = l_Lean_registerTraceClass(v___x_2389_, v___x_2390_, v___x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2____boxed(lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_();
return v_res_2394_;
}
}
lean_object* runtime_initialize_Lean_Elab_DeclNameGen(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DeclUtil(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DefView(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot = _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot();
lean_mark_persistent(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot);
l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot = _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot();
lean_mark_persistent(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot);
l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot = _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot();
lean_mark_persistent(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot);
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
