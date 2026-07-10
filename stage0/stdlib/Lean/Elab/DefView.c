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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(lean_object* v___f_154_, lean_object* v_x_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_x_155_, v___f_154_, v___y_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed(lean_object* v___f_158_, lean_object* v_x_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(v___f_158_, v_x_159_, v___y_160_);
lean_dec_ref(v___y_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1(lean_object* v___x_162_, lean_object* v___f_163_, lean_object* v_s_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_toSnapshot_166_; lean_object* v_moreSnaps_167_; lean_object* v___x_168_; size_t v_sz_169_; size_t v___x_170_; lean_object* v___x_248__overap_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_toSnapshot_166_ = lean_ctor_get(v_s_164_, 0);
lean_inc_ref(v_toSnapshot_166_);
v_moreSnaps_167_ = lean_ctor_get(v_s_164_, 3);
lean_inc_ref(v_moreSnaps_167_);
lean_dec_ref(v_s_164_);
v___x_168_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_166_, v___y_165_);
v_sz_169_ = lean_array_size(v_moreSnaps_167_);
v___x_170_ = ((size_t)0ULL);
v___x_248__overap_171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_162_, v___f_163_, v_sz_169_, v___x_170_, v_moreSnaps_167_);
lean_inc_ref(v___y_165_);
v___x_172_ = lean_apply_1(v___x_248__overap_171_, v___y_165_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_168_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1___boxed(lean_object* v___x_174_, lean_object* v___f_175_, lean_object* v_s_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1(v___x_174_, v___f_175_, v_s_176_, v___y_177_);
lean_dec_ref(v___y_177_);
return v_res_178_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__9));
v___x_199_ = l_ReaderT_instMonad___redArg(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13(void){
_start:
{
lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___f_205_; 
v___f_203_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__12));
v___x_204_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10);
v___f_205_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1___boxed), 4, 2);
lean_closure_set(v___f_205_, 0, v___x_204_);
lean_closure_set(v___f_205_, 1, v___f_203_);
return v___f_205_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot(void){
_start:
{
lean_object* v___f_206_; 
v___f_206_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13);
return v___f_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(lean_object* v___x_207_, lean_object* v_x_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_x_208_, v___x_207_, v___y_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(lean_object* v___x_211_, lean_object* v_x_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(v___x_211_, v_x_212_, v___y_213_);
lean_dec_ref(v___y_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2(lean_object* v___x_217_, lean_object* v___f_218_, lean_object* v___f_219_, lean_object* v___f_220_, lean_object* v_s_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_toSnapshot_223_; lean_object* v_tacSnap_x3f_224_; lean_object* v_bodySnap_225_; lean_object* v_moreSnaps_226_; lean_object* v___x_227_; lean_object* v___y_229_; 
v_toSnapshot_223_ = lean_ctor_get(v_s_221_, 0);
lean_inc_ref(v_toSnapshot_223_);
v_tacSnap_x3f_224_ = lean_ctor_get(v_s_221_, 4);
lean_inc(v_tacSnap_x3f_224_);
v_bodySnap_225_ = lean_ctor_get(v_s_221_, 6);
lean_inc_ref(v_bodySnap_225_);
v_moreSnaps_226_ = lean_ctor_get(v_s_221_, 7);
lean_inc_ref(v_moreSnaps_226_);
lean_dec_ref(v_s_221_);
v___x_227_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_223_, v___y_222_);
if (lean_obj_tag(v_tacSnap_x3f_224_) == 0)
{
lean_object* v___x_244_; 
v___x_244_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___closed__0));
v___y_229_ = v___x_244_;
goto v___jp_228_;
}
else
{
lean_object* v_val_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_val_245_ = lean_ctor_get(v_tacSnap_x3f_224_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v_tacSnap_x3f_224_, 1);
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_mk_empty_array_with_capacity(v___x_246_);
v___x_248_ = lean_array_push(v___x_247_, v_val_245_);
v___y_229_ = v___x_248_;
goto v___jp_228_;
}
v___jp_228_:
{
size_t v_sz_230_; size_t v___x_231_; lean_object* v___x_510__overap_232_; lean_object* v___x_233_; lean_object* v___x_234_; size_t v_sz_235_; lean_object* v___x_512__overap_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_sz_230_ = lean_array_size(v___y_229_);
v___x_231_ = ((size_t)0ULL);
lean_inc_ref(v___x_217_);
v___x_510__overap_232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_217_, v___f_218_, v_sz_230_, v___x_231_, v___y_229_);
lean_inc_ref_n(v___y_222_, 2);
v___x_233_ = lean_apply_1(v___x_510__overap_232_, v___y_222_);
v___x_234_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_bodySnap_225_, v___f_219_, v___y_222_);
v_sz_235_ = lean_array_size(v_moreSnaps_226_);
v___x_512__overap_236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_217_, v___f_220_, v_sz_235_, v___x_231_, v_moreSnaps_226_);
v___x_237_ = lean_apply_1(v___x_512__overap_236_, v___y_222_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_mk_empty_array_with_capacity(v___x_238_);
v___x_240_ = lean_array_push(v___x_239_, v___x_234_);
v___x_241_ = l_Array_append___redArg(v___x_233_, v___x_240_);
lean_dec_ref(v___x_240_);
v___x_242_ = l_Array_append___redArg(v___x_241_, v___x_237_);
lean_dec_ref(v___x_237_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_227_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___boxed(lean_object* v___x_249_, lean_object* v___f_250_, lean_object* v___f_251_, lean_object* v___f_252_, lean_object* v_s_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2(v___x_249_, v___f_250_, v___f_251_, v___f_252_, v_s_253_, v___y_254_);
lean_dec_ref(v___y_254_);
return v_res_255_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2(void){
_start:
{
lean_object* v___x_259_; lean_object* v___f_260_; 
v___x_259_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot;
v___f_260_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_260_, 0, v___x_259_);
return v___f_260_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3(void){
_start:
{
lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___f_265_; 
v___f_261_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__12));
v___f_262_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2, &l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2_once, _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2);
v___f_263_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1));
v___x_264_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10);
v___f_265_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___boxed), 6, 4);
lean_closure_set(v___f_265_, 0, v___x_264_);
lean_closure_set(v___f_265_, 1, v___f_263_);
lean_closure_set(v___f_265_, 2, v___f_262_);
lean_closure_set(v___f_265_, 3, v___f_261_);
return v___f_265_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot(void){
_start:
{
lean_object* v___f_266_; 
v___f_266_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3, &l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3_once, _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3);
return v___f_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(lean_object* v___f_276_, lean_object* v_x_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_headerProcessedSnap_279_; lean_object* v___x_280_; 
v_headerProcessedSnap_279_ = lean_ctor_get(v_x_277_, 1);
lean_inc_ref(v_headerProcessedSnap_279_);
lean_dec_ref(v_x_277_);
v___x_280_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_headerProcessedSnap_279_, v___f_276_, v___y_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0___boxed(lean_object* v___f_281_, lean_object* v_x_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(v___f_281_, v_x_282_, v___y_283_);
lean_dec_ref(v___y_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(lean_object* v___x_285_, lean_object* v___f_286_, lean_object* v_s_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_toSnapshot_289_; lean_object* v_defs_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_302_; 
v_toSnapshot_289_ = lean_ctor_get(v_s_287_, 0);
v_defs_290_ = lean_ctor_get(v_s_287_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v_s_287_);
if (v_isSharedCheck_302_ == 0)
{
v___x_292_ = v_s_287_;
v_isShared_293_ = v_isSharedCheck_302_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_defs_290_);
lean_inc(v_toSnapshot_289_);
lean_dec(v_s_287_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_302_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; size_t v_sz_295_; size_t v___x_296_; lean_object* v___x_252__overap_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_294_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_289_, v___y_288_);
v_sz_295_ = lean_array_size(v_defs_290_);
v___x_296_ = ((size_t)0ULL);
v___x_252__overap_297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_285_, v___f_286_, v_sz_295_, v___x_296_, v_defs_290_);
lean_inc_ref(v___y_288_);
v___x_298_ = lean_apply_1(v___x_252__overap_297_, v___y_288_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v___x_298_);
lean_ctor_set(v___x_292_, 0, v___x_294_);
v___x_300_ = v___x_292_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1___boxed(lean_object* v___x_303_, lean_object* v___f_304_, lean_object* v_s_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(v___x_303_, v___f_304_, v_s_305_, v___y_306_);
lean_dec_ref(v___y_306_);
return v_res_307_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0(void){
_start:
{
lean_object* v___x_308_; lean_object* v___f_309_; 
v___x_308_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot;
v___f_309_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_309_, 0, v___x_308_);
return v___f_309_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1(void){
_start:
{
lean_object* v___f_310_; lean_object* v___f_311_; 
v___f_310_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0, &l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_once, _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0);
v___f_311_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0___boxed), 3, 1);
lean_closure_set(v___f_311_, 0, v___f_310_);
return v___f_311_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2(void){
_start:
{
lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v___f_314_; 
v___f_312_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1, &l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_once, _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1);
v___x_313_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10);
v___f_314_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1___boxed), 4, 2);
lean_closure_set(v___f_314_, 0, v___x_313_);
lean_closure_set(v___f_314_, 1, v___f_312_);
return v___f_314_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot(void){
_start:
{
lean_object* v___f_315_; 
v___f_315_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2, &l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_once, _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2);
return v___f_315_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView_default___closed__0(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; 
v___x_316_ = lean_box(0);
v___x_317_ = l_Lean_Elab_instInhabitedModifiers_default;
v___x_318_ = lean_box(0);
v___x_319_ = 0;
v___x_320_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
lean_ctor_set(v___x_320_, 2, v___x_317_);
lean_ctor_set(v___x_320_, 3, v___x_318_);
lean_ctor_set(v___x_320_, 4, v___x_318_);
lean_ctor_set(v___x_320_, 5, v___x_316_);
lean_ctor_set(v___x_320_, 6, v___x_318_);
lean_ctor_set(v___x_320_, 7, v___x_316_);
lean_ctor_set(v___x_320_, 8, v___x_316_);
lean_ctor_set(v___x_320_, 9, v___x_316_);
lean_ctor_set_uint8(v___x_320_, sizeof(void*)*10, v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView_default(void){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Lean_Elab_instInhabitedDefView_default___closed__0, &l_Lean_Elab_instInhabitedDefView_default___closed__0_once, _init_l_Lean_Elab_instInhabitedDefView_default___closed__0);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView(void){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Elab_instInhabitedDefView_default;
return v___x_322_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(lean_object* v_as_326_, size_t v_i_327_, size_t v_stop_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_eq(v_i_327_, v_stop_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v_name_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_330_ = lean_array_uget_borrowed(v_as_326_, v_i_327_);
v_name_331_ = lean_ctor_get(v___x_330_, 0);
v___x_332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1));
v___x_333_ = lean_name_eq(v_name_331_, v___x_332_);
if (v___x_333_ == 0)
{
size_t v___x_334_; size_t v___x_335_; 
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_add(v_i_327_, v___x_334_);
v_i_327_ = v___x_335_;
goto _start;
}
else
{
return v___x_333_;
}
}
else
{
uint8_t v___x_337_; 
v___x_337_ = 0;
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___boxed(lean_object* v_as_338_, lean_object* v_i_339_, lean_object* v_stop_340_){
_start:
{
size_t v_i_boxed_341_; size_t v_stop_boxed_342_; uint8_t v_res_343_; lean_object* v_r_344_; 
v_i_boxed_341_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_stop_boxed_342_ = lean_unbox_usize(v_stop_340_);
lean_dec(v_stop_340_);
v_res_343_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_as_338_, v_i_boxed_341_, v_stop_boxed_342_);
lean_dec_ref(v_as_338_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_isInstance(lean_object* v_view_345_){
_start:
{
lean_object* v_modifiers_346_; lean_object* v_attrs_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_modifiers_346_ = lean_ctor_get(v_view_345_, 2);
v_attrs_347_ = lean_ctor_get(v_modifiers_346_, 2);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_array_get_size(v_attrs_347_);
v___x_350_ = lean_nat_dec_lt(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
return v___x_350_;
}
else
{
if (v___x_350_ == 0)
{
return v___x_350_;
}
else
{
size_t v___x_351_; size_t v___x_352_; uint8_t v___x_353_; 
v___x_351_ = ((size_t)0ULL);
v___x_352_ = lean_usize_of_nat(v___x_349_);
v___x_353_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_attrs_347_, v___x_351_, v___x_352_);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_isInstance___boxed(lean_object* v_view_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lean_Elab_DefView_isInstance(v_view_354_);
lean_dec_ref(v_view_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_markDefEq___lam__0(lean_object* v_x_360_){
_start:
{
lean_object* v_name_361_; lean_object* v___x_362_; uint8_t v___x_363_; uint8_t v___x_364_; 
v_name_361_ = lean_ctor_get(v_x_360_, 0);
v___x_362_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___lam__0___closed__1));
v___x_363_ = lean_name_eq(v_name_361_, v___x_362_);
v___x_364_ = lean_bool_not(v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_markDefEq___lam__0___boxed(lean_object* v_x_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Lean_Elab_DefView_markDefEq___lam__0(v_x_365_);
lean_dec_ref(v_x_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_markDefEq(lean_object* v_view_373_){
_start:
{
uint8_t v_kind_374_; lean_object* v_ref_375_; lean_object* v_headerRef_376_; lean_object* v_modifiers_377_; lean_object* v_declId_378_; lean_object* v_binders_379_; lean_object* v_type_x3f_380_; lean_object* v_value_381_; lean_object* v_docString_x3f_382_; lean_object* v_headerSnap_x3f_383_; lean_object* v_deriving_x3f_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_395_; 
v_kind_374_ = lean_ctor_get_uint8(v_view_373_, sizeof(void*)*10);
v_ref_375_ = lean_ctor_get(v_view_373_, 0);
v_headerRef_376_ = lean_ctor_get(v_view_373_, 1);
v_modifiers_377_ = lean_ctor_get(v_view_373_, 2);
v_declId_378_ = lean_ctor_get(v_view_373_, 3);
v_binders_379_ = lean_ctor_get(v_view_373_, 4);
v_type_x3f_380_ = lean_ctor_get(v_view_373_, 5);
v_value_381_ = lean_ctor_get(v_view_373_, 6);
v_docString_x3f_382_ = lean_ctor_get(v_view_373_, 7);
v_headerSnap_x3f_383_ = lean_ctor_get(v_view_373_, 8);
v_deriving_x3f_384_ = lean_ctor_get(v_view_373_, 9);
v_isSharedCheck_395_ = !lean_is_exclusive(v_view_373_);
if (v_isSharedCheck_395_ == 0)
{
v___x_386_ = v_view_373_;
v_isShared_387_ = v_isSharedCheck_395_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_deriving_x3f_384_);
lean_inc(v_headerSnap_x3f_383_);
lean_inc(v_docString_x3f_382_);
lean_inc(v_value_381_);
lean_inc(v_type_x3f_380_);
lean_inc(v_binders_379_);
lean_inc(v_declId_378_);
lean_inc(v_modifiers_377_);
lean_inc(v_headerRef_376_);
lean_inc(v_ref_375_);
lean_dec(v_view_373_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_395_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___f_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___f_388_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___closed__0));
v___x_389_ = l_Lean_Elab_Modifiers_filterAttrs(v_modifiers_377_, v___f_388_);
v___x_390_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___closed__1));
v___x_391_ = l_Lean_Elab_Modifiers_addFirstAttr(v___x_389_, v___x_390_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 2, v___x_391_);
v___x_393_ = v___x_386_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_ref_375_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_headerRef_376_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_declId_378_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v_binders_379_);
lean_ctor_set(v_reuseFailAlloc_394_, 5, v_type_x3f_380_);
lean_ctor_set(v_reuseFailAlloc_394_, 6, v_value_381_);
lean_ctor_set(v_reuseFailAlloc_394_, 7, v_docString_x3f_382_);
lean_ctor_set(v_reuseFailAlloc_394_, 8, v_headerSnap_x3f_383_);
lean_ctor_set(v_reuseFailAlloc_394_, 9, v_deriving_x3f_384_);
lean_ctor_set_uint8(v_reuseFailAlloc_394_, sizeof(void*)*10, v_kind_374_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev(lean_object* v_modifiers_413_, lean_object* v_stx_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_fst_418_; lean_object* v_snd_419_; lean_object* v___x_420_; lean_object* v_modifiers_421_; lean_object* v___x_422_; lean_object* v_modifiers_423_; lean_object* v_docString_x3f_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_415_ = lean_unsigned_to_nat(2u);
v___x_416_ = l_Lean_Syntax_getArg(v_stx_414_, v___x_415_);
v___x_417_ = l_Lean_Elab_expandOptDeclSig(v___x_416_);
lean_dec(v___x_416_);
v_fst_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_fst_418_);
v_snd_419_ = lean_ctor_get(v___x_417_, 1);
lean_inc(v_snd_419_);
lean_dec_ref(v___x_417_);
v___x_420_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2));
v_modifiers_421_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_413_, v___x_420_);
v___x_422_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5));
v_modifiers_423_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_421_, v___x_422_);
v_docString_x3f_424_ = lean_ctor_get(v_modifiers_423_, 1);
lean_inc(v_docString_x3f_424_);
v___x_425_ = 5;
v___x_426_ = l_Lean_Syntax_getArgs(v_stx_414_);
v___x_427_ = lean_unsigned_to_nat(3u);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = l_Array_toSubarray___redArg(v___x_426_, v___x_428_, v___x_427_);
v___x_430_ = l_Subarray_copy___redArg(v___x_429_);
v___x_431_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_432_ = lean_box(2);
v___x_433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_431_);
lean_ctor_set(v___x_433_, 2, v___x_430_);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = l_Lean_Syntax_getArg(v_stx_414_, v___x_434_);
v___x_436_ = l_Lean_Syntax_getArg(v_stx_414_, v___x_427_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_438_, 0, v_stx_414_);
lean_ctor_set(v___x_438_, 1, v___x_433_);
lean_ctor_set(v___x_438_, 2, v_modifiers_423_);
lean_ctor_set(v___x_438_, 3, v___x_435_);
lean_ctor_set(v___x_438_, 4, v_fst_418_);
lean_ctor_set(v___x_438_, 5, v_snd_419_);
lean_ctor_set(v___x_438_, 6, v___x_436_);
lean_ctor_set(v___x_438_, 7, v_docString_x3f_424_);
lean_ctor_set(v___x_438_, 8, v___x_437_);
lean_ctor_set(v___x_438_, 9, v___x_437_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*10, v___x_425_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfDef(lean_object* v_modifiers_439_, lean_object* v_stx_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___y_447_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_441_ = lean_unsigned_to_nat(2u);
v___x_442_ = l_Lean_Syntax_getArg(v_stx_440_, v___x_441_);
v___x_443_ = l_Lean_Elab_expandOptDeclSig(v___x_442_);
lean_dec(v___x_442_);
v_fst_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_fst_444_);
v_snd_445_ = lean_ctor_get(v___x_443_, 1);
lean_inc(v_snd_445_);
lean_dec_ref(v___x_443_);
v___x_463_ = lean_unsigned_to_nat(4u);
v___x_464_ = l_Lean_Syntax_getArg(v_stx_440_, v___x_463_);
v___x_465_ = l_Lean_Syntax_isNone(v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = l_Lean_Syntax_getArg(v___x_464_, v___x_466_);
lean_dec(v___x_464_);
v___x_468_ = l_Lean_Syntax_getSepArgs(v___x_467_);
lean_dec(v___x_467_);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
v___y_447_ = v___x_469_;
goto v___jp_446_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v___x_464_);
v___x_470_ = lean_box(0);
v___y_447_ = v___x_470_;
goto v___jp_446_;
}
v___jp_446_:
{
lean_object* v_docString_x3f_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_docString_x3f_448_ = lean_ctor_get(v_modifiers_439_, 1);
lean_inc(v_docString_x3f_448_);
v___x_449_ = 0;
v___x_450_ = l_Lean_Syntax_getArgs(v_stx_440_);
v___x_451_ = lean_unsigned_to_nat(3u);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = l_Array_toSubarray___redArg(v___x_450_, v___x_452_, v___x_451_);
v___x_454_ = l_Subarray_copy___redArg(v___x_453_);
v___x_455_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_456_ = lean_box(2);
v___x_457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
lean_ctor_set(v___x_457_, 2, v___x_454_);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = l_Lean_Syntax_getArg(v_stx_440_, v___x_458_);
v___x_460_ = l_Lean_Syntax_getArg(v_stx_440_, v___x_451_);
v___x_461_ = lean_box(0);
v___x_462_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_462_, 0, v_stx_440_);
lean_ctor_set(v___x_462_, 1, v___x_457_);
lean_ctor_set(v___x_462_, 2, v_modifiers_439_);
lean_ctor_set(v___x_462_, 3, v___x_459_);
lean_ctor_set(v___x_462_, 4, v_fst_444_);
lean_ctor_set(v___x_462_, 5, v_snd_445_);
lean_ctor_set(v___x_462_, 6, v___x_460_);
lean_ctor_set(v___x_462_, 7, v_docString_x3f_448_);
lean_ctor_set(v___x_462_, 8, v___x_461_);
lean_ctor_set(v___x_462_, 9, v___y_447_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*10, v___x_449_);
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem(lean_object* v_modifiers_471_, lean_object* v_stx_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_fst_476_; lean_object* v_snd_477_; lean_object* v_docString_x3f_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_473_ = lean_unsigned_to_nat(2u);
v___x_474_ = l_Lean_Syntax_getArg(v_stx_472_, v___x_473_);
v___x_475_ = l_Lean_Elab_expandDeclSig(v___x_474_);
lean_dec(v___x_474_);
v_fst_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_fst_476_);
v_snd_477_ = lean_ctor_get(v___x_475_, 1);
lean_inc(v_snd_477_);
lean_dec_ref(v___x_475_);
v_docString_x3f_478_ = lean_ctor_get(v_modifiers_471_, 1);
lean_inc(v_docString_x3f_478_);
v___x_479_ = 2;
v___x_480_ = l_Lean_Syntax_getArgs(v_stx_472_);
v___x_481_ = lean_unsigned_to_nat(3u);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = l_Array_toSubarray___redArg(v___x_480_, v___x_482_, v___x_481_);
v___x_484_ = l_Subarray_copy___redArg(v___x_483_);
v___x_485_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_486_ = lean_box(2);
v___x_487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_484_);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = l_Lean_Syntax_getArg(v_stx_472_, v___x_488_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_snd_477_);
v___x_491_ = l_Lean_Syntax_getArg(v_stx_472_, v___x_481_);
v___x_492_ = lean_box(0);
v___x_493_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_493_, 0, v_stx_472_);
lean_ctor_set(v___x_493_, 1, v___x_487_);
lean_ctor_set(v___x_493_, 2, v_modifiers_471_);
lean_ctor_set(v___x_493_, 3, v___x_489_);
lean_ctor_set(v___x_493_, 4, v_fst_476_);
lean_ctor_set(v___x_493_, 5, v___x_490_);
lean_ctor_set(v___x_493_, 6, v___x_491_);
lean_ctor_set(v___x_493_, 7, v_docString_x3f_478_);
lean_ctor_set(v___x_493_, 8, v___x_492_);
lean_ctor_set(v___x_493_, 9, v___x_492_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*10, v___x_479_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; lean_object* v_env_497_; lean_object* v___x_498_; lean_object* v_mainModule_499_; lean_object* v___x_500_; 
v___x_496_ = lean_st_ref_get(v___y_494_);
v_env_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc_ref(v_env_497_);
lean_dec(v___x_496_);
v___x_498_ = l_Lean_Environment_header(v_env_497_);
lean_dec_ref(v_env_497_);
v_mainModule_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_mainModule_499_);
lean_dec_ref(v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v_mainModule_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg___boxed(lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_501_);
lean_dec(v___y_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___boxed(lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = l_Lean_maxRecDepthErrorMessage;
v___x_518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3);
v___x_520_ = l_Lean_MessageData_ofFormat(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4);
v___x_522_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2));
v___x_523_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v___x_521_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(lean_object* v_ref_524_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_ref_524_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___boxed(lean_object* v_ref_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(lean_object* v_x_532_, lean_object* v___y_533_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_535_; 
v_a_534_ = lean_ctor_get(v_x_532_, 0);
lean_inc(v_a_534_);
v___x_535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_535_, 0, v_a_534_);
lean_ctor_set(v___x_535_, 1, v___y_533_);
return v___x_535_;
}
else
{
lean_object* v_a_536_; lean_object* v___x_537_; 
v_a_536_ = lean_ctor_get(v_x_532_, 0);
lean_inc(v_a_536_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_a_536_);
lean_ctor_set(v___x_537_, 1, v___y_533_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg___boxed(lean_object* v_x_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_538_, v___y_539_);
lean_dec_ref(v_x_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(lean_object* v_env_541_, lean_object* v_stx_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_541_, v_stx_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
if (lean_obj_tag(v_a_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_a_547_ = lean_ctor_get(v___x_545_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v___x_545_, 0);
lean_dec(v_unused_556_);
v___x_549_ = v___x_545_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_box(0);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_a_547_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
lean_object* v_val_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_585_; 
v_val_557_ = lean_ctor_get(v_a_546_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v_a_546_);
if (v_isSharedCheck_585_ == 0)
{
v___x_559_ = v_a_546_;
v_isShared_560_ = v_isSharedCheck_585_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_val_557_);
lean_dec(v_a_546_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_585_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v_snd_561_; 
v_snd_561_ = lean_ctor_get(v_val_557_, 1);
lean_inc(v_snd_561_);
lean_dec(v_val_557_);
if (lean_obj_tag(v_snd_561_) == 0)
{
lean_object* v_a_562_; lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_571_; 
lean_del_object(v___x_559_);
v_a_562_ = lean_ctor_get(v___x_545_, 1);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_545_, 2);
v_a_563_ = lean_ctor_get(v_snd_561_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v_snd_561_);
if (v_isSharedCheck_571_ == 0)
{
v___x_565_ = v_snd_561_;
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v_snd_561_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_570_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; 
v___x_569_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_568_, v_a_562_);
lean_dec_ref(v___x_568_);
return v___x_569_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_584_; 
v_a_572_ = lean_ctor_get(v___x_545_, 1);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_545_, 2);
v_a_573_ = lean_ctor_get(v_snd_561_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_snd_561_);
if (v_isSharedCheck_584_ == 0)
{
v___x_575_ = v_snd_561_;
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v_snd_561_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v_a_573_);
v___x_578_ = v___x_559_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_583_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_580_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_578_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_582_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; 
v___x_581_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_580_, v_a_572_);
lean_dec_ref(v___x_580_);
return v___x_581_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
v_a_586_ = lean_ctor_get(v___x_545_, 0);
v_a_587_ = lean_ctor_get(v___x_545_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_545_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_inc(v_a_586_);
lean_dec(v___x_545_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_586_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed(lean_object* v_env_595_, lean_object* v_stx_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(v_env_595_, v_stx_596_, v___y_597_, v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(lean_object* v_env_600_, lean_object* v_currNamespace_601_, lean_object* v_openDecls_602_, lean_object* v_n_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = l_Lean_ResolveName_resolveNamespace(v_env_600_, v_currNamespace_601_, v_openDecls_602_, v_n_603_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___y_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed(lean_object* v_env_608_, lean_object* v_currNamespace_609_, lean_object* v_openDecls_610_, lean_object* v_n_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(v_env_608_, v_currNamespace_609_, v_openDecls_610_, v_n_611_, v___y_612_, v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(lean_object* v_currNamespace_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_currNamespace_615_);
lean_ctor_set(v___x_618_, 1, v___y_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(v_currNamespace_619_, v___y_620_, v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_622_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_box(0);
v___x_624_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg(){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___boxed(lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v_res_630_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_631_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
lean_ctor_set(v___x_636_, 2, v___x_635_);
lean_ctor_set(v___x_636_, 3, v___x_635_);
lean_ctor_set(v___x_636_, 4, v___x_634_);
lean_ctor_set(v___x_636_, 5, v___x_634_);
lean_ctor_set(v___x_636_, 6, v___x_634_);
lean_ctor_set(v___x_636_, 7, v___x_634_);
lean_ctor_set(v___x_636_, 8, v___x_634_);
lean_ctor_set(v___x_636_, 9, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_unsigned_to_nat(32u);
v___x_638_ = lean_mk_empty_array_with_capacity(v___x_637_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_640_ = ((size_t)5ULL);
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_unsigned_to_nat(32u);
v___x_643_ = lean_mk_empty_array_with_capacity(v___x_642_);
v___x_644_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3);
v___x_645_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_643_);
lean_ctor_set(v___x_645_, 2, v___x_641_);
lean_ctor_set(v___x_645_, 3, v___x_641_);
lean_ctor_set_usize(v___x_645_, 4, v___x_640_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_646_ = lean_box(1);
v___x_647_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4);
v___x_648_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
v___x_649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_647_);
lean_ctor_set(v___x_649_, 2, v___x_646_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(lean_object* v_msgData_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; lean_object* v_env_654_; lean_object* v___x_655_; lean_object* v_scopes_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_opts_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_653_ = lean_st_ref_get(v___y_651_);
v_env_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc_ref(v_env_654_);
lean_dec(v___x_653_);
v___x_655_ = lean_st_ref_get(v___y_651_);
v_scopes_656_ = lean_ctor_get(v___x_655_, 2);
lean_inc(v_scopes_656_);
lean_dec(v___x_655_);
v___x_657_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_658_ = l_List_head_x21___redArg(v___x_657_, v_scopes_656_);
lean_dec(v_scopes_656_);
v_opts_659_ = lean_ctor_get(v___x_658_, 1);
lean_inc_ref(v_opts_659_);
lean_dec(v___x_658_);
v___x_660_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2);
v___x_661_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5);
v___x_662_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_662_, 0, v_env_654_);
lean_ctor_set(v___x_662_, 1, v___x_660_);
lean_ctor_set(v___x_662_, 2, v___x_661_);
lean_ctor_set(v___x_662_, 3, v_opts_659_);
v___x_663_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v_msgData_650_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___boxed(lean_object* v_msgData_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_665_, v___y_666_);
lean_dec(v___y_666_);
return v_res_668_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0(void){
_start:
{
lean_object* v___x_669_; double v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_float_of_nat(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(lean_object* v_cls_674_, lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Elab_Command_getRef___redArg(v___y_676_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_681_; lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_728_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_675_, v___y_677_);
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_728_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_728_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_728_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v_traceState_687_; lean_object* v_env_688_; lean_object* v_messages_689_; lean_object* v_scopes_690_; lean_object* v_usedQuotCtxts_691_; lean_object* v_nextMacroScope_692_; lean_object* v_maxRecDepth_693_; lean_object* v_ngen_694_; lean_object* v_auxDeclNGen_695_; lean_object* v_infoState_696_; lean_object* v_snapshotTasks_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_727_; 
v___x_686_ = lean_st_ref_take(v___y_677_);
v_traceState_687_ = lean_ctor_get(v___x_686_, 9);
v_env_688_ = lean_ctor_get(v___x_686_, 0);
v_messages_689_ = lean_ctor_get(v___x_686_, 1);
v_scopes_690_ = lean_ctor_get(v___x_686_, 2);
v_usedQuotCtxts_691_ = lean_ctor_get(v___x_686_, 3);
v_nextMacroScope_692_ = lean_ctor_get(v___x_686_, 4);
v_maxRecDepth_693_ = lean_ctor_get(v___x_686_, 5);
v_ngen_694_ = lean_ctor_get(v___x_686_, 6);
v_auxDeclNGen_695_ = lean_ctor_get(v___x_686_, 7);
v_infoState_696_ = lean_ctor_get(v___x_686_, 8);
v_snapshotTasks_697_ = lean_ctor_get(v___x_686_, 10);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_727_ == 0)
{
v___x_699_ = v___x_686_;
v_isShared_700_ = v_isSharedCheck_727_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_snapshotTasks_697_);
lean_inc(v_traceState_687_);
lean_inc(v_infoState_696_);
lean_inc(v_auxDeclNGen_695_);
lean_inc(v_ngen_694_);
lean_inc(v_maxRecDepth_693_);
lean_inc(v_nextMacroScope_692_);
lean_inc(v_usedQuotCtxts_691_);
lean_inc(v_scopes_690_);
lean_inc(v_messages_689_);
lean_inc(v_env_688_);
lean_dec(v___x_686_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_727_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
uint64_t v_tid_701_; lean_object* v_traces_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_726_; 
v_tid_701_ = lean_ctor_get_uint64(v_traceState_687_, sizeof(void*)*1);
v_traces_702_ = lean_ctor_get(v_traceState_687_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v_traceState_687_);
if (v_isSharedCheck_726_ == 0)
{
v___x_704_ = v_traceState_687_;
v_isShared_705_ = v_isSharedCheck_726_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_traces_702_);
lean_dec(v_traceState_687_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_726_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; double v___x_707_; uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_706_ = lean_box(0);
v___x_707_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0);
v___x_708_ = 0;
v___x_709_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1));
v___x_710_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_710_, 0, v_cls_674_);
lean_ctor_set(v___x_710_, 1, v___x_706_);
lean_ctor_set(v___x_710_, 2, v___x_709_);
lean_ctor_set_float(v___x_710_, sizeof(void*)*3, v___x_707_);
lean_ctor_set_float(v___x_710_, sizeof(void*)*3 + 8, v___x_707_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*3 + 16, v___x_708_);
v___x_711_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2));
v___x_712_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v_a_682_);
lean_ctor_set(v___x_712_, 2, v___x_711_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_a_680_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_PersistentArray_push___redArg(v_traces_702_, v___x_713_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_714_);
v___x_716_ = v___x_704_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_714_);
lean_ctor_set_uint64(v_reuseFailAlloc_725_, sizeof(void*)*1, v_tid_701_);
v___x_716_ = v_reuseFailAlloc_725_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 9, v___x_716_);
v___x_718_ = v___x_699_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_env_688_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_messages_689_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_scopes_690_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_usedQuotCtxts_691_);
lean_ctor_set(v_reuseFailAlloc_724_, 4, v_nextMacroScope_692_);
lean_ctor_set(v_reuseFailAlloc_724_, 5, v_maxRecDepth_693_);
lean_ctor_set(v_reuseFailAlloc_724_, 6, v_ngen_694_);
lean_ctor_set(v_reuseFailAlloc_724_, 7, v_auxDeclNGen_695_);
lean_ctor_set(v_reuseFailAlloc_724_, 8, v_infoState_696_);
lean_ctor_set(v_reuseFailAlloc_724_, 9, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_724_, 10, v_snapshotTasks_697_);
v___x_718_ = v_reuseFailAlloc_724_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_719_ = lean_st_ref_set(v___y_677_, v___x_718_);
v___x_720_ = lean_box(0);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_720_);
v___x_722_ = v___x_684_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v_msg_675_);
lean_dec(v_cls_674_);
v_a_729_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_679_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_679_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___boxed(lean_object* v_cls_737_, lean_object* v_msg_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_cls_737_, v_msg_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_742_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(lean_object* v_keys_743_, lean_object* v_i_744_, lean_object* v_k_745_){
_start:
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_array_get_size(v_keys_743_);
v___x_747_ = lean_nat_dec_lt(v_i_744_, v___x_746_);
if (v___x_747_ == 0)
{
lean_dec(v_i_744_);
return v___x_747_;
}
else
{
lean_object* v_k_x27_748_; uint8_t v___x_749_; 
v_k_x27_748_ = lean_array_fget_borrowed(v_keys_743_, v_i_744_);
v___x_749_ = l_Lean_instBEqExtraModUse_beq(v_k_745_, v_k_x27_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = lean_nat_add(v_i_744_, v___x_750_);
lean_dec(v_i_744_);
v_i_744_ = v___x_751_;
goto _start;
}
else
{
lean_dec(v_i_744_);
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg___boxed(lean_object* v_keys_753_, lean_object* v_i_754_, lean_object* v_k_755_){
_start:
{
uint8_t v_res_756_; lean_object* v_r_757_; 
v_res_756_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_753_, v_i_754_, v_k_755_);
lean_dec_ref(v_k_755_);
lean_dec_ref(v_keys_753_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(lean_object* v_x_758_, size_t v_x_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
lean_object* v_es_761_; lean_object* v___x_762_; size_t v___x_763_; size_t v___x_764_; lean_object* v_j_765_; lean_object* v___x_766_; 
v_es_761_ = lean_ctor_get(v_x_758_, 0);
v___x_762_ = lean_box(2);
v___x_763_ = ((size_t)31ULL);
v___x_764_ = lean_usize_land(v_x_759_, v___x_763_);
v_j_765_ = lean_usize_to_nat(v___x_764_);
v___x_766_ = lean_array_get_borrowed(v___x_762_, v_es_761_, v_j_765_);
lean_dec(v_j_765_);
switch(lean_obj_tag(v___x_766_))
{
case 0:
{
lean_object* v_key_767_; uint8_t v___x_768_; 
v_key_767_ = lean_ctor_get(v___x_766_, 0);
v___x_768_ = l_Lean_instBEqExtraModUse_beq(v_x_760_, v_key_767_);
return v___x_768_;
}
case 1:
{
lean_object* v_node_769_; size_t v___x_770_; size_t v___x_771_; 
v_node_769_ = lean_ctor_get(v___x_766_, 0);
v___x_770_ = ((size_t)5ULL);
v___x_771_ = lean_usize_shift_right(v_x_759_, v___x_770_);
v_x_758_ = v_node_769_;
v_x_759_ = v___x_771_;
goto _start;
}
default: 
{
uint8_t v___x_773_; 
v___x_773_ = 0;
return v___x_773_;
}
}
}
else
{
lean_object* v_ks_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_ks_774_ = lean_ctor_get(v_x_758_, 0);
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_ks_774_, v___x_775_, v_x_760_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
size_t v_x_16981__boxed_780_; uint8_t v_res_781_; lean_object* v_r_782_; 
v_x_16981__boxed_780_ = lean_unbox_usize(v_x_778_);
lean_dec(v_x_778_);
v_res_781_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_777_, v_x_16981__boxed_780_, v_x_779_);
lean_dec_ref(v_x_779_);
lean_dec_ref(v_x_777_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
uint64_t v___x_785_; size_t v___x_786_; uint8_t v___x_787_; 
v___x_785_ = l_Lean_instHashableExtraModUse_hash(v_x_784_);
v___x_786_ = lean_uint64_to_usize(v___x_785_);
v___x_787_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_783_, v___x_786_, v_x_784_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_788_, v_x_789_);
lean_dec_ref(v_x_789_);
lean_dec_ref(v_x_788_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1));
v___x_795_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0));
v___x_796_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_795_, v___x_794_);
return v___x_796_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5));
v___x_802_ = l_Lean_stringToMessageData(v___x_801_);
return v___x_802_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7));
v___x_805_ = l_Lean_stringToMessageData(v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1));
v___x_807_ = l_Lean_stringToMessageData(v___x_806_);
return v___x_807_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_cls_811_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4));
v___x_812_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11));
v___x_813_ = l_Lean_Name_append(v___x_812_, v_cls_811_);
return v___x_813_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13));
v___x_816_ = l_Lean_stringToMessageData(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15));
v___x_819_ = l_Lean_stringToMessageData(v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(lean_object* v_mod_824_, uint8_t v_isMeta_825_, lean_object* v_hint_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; lean_object* v_env_831_; uint8_t v_isExporting_832_; lean_object* v___x_833_; lean_object* v_env_834_; lean_object* v___x_835_; lean_object* v_entry_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___y_841_; lean_object* v___x_867_; uint8_t v___x_868_; uint8_t v___x_869_; 
v___x_830_ = lean_st_ref_get(v___y_828_);
v_env_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc_ref(v_env_831_);
lean_dec(v___x_830_);
v_isExporting_832_ = lean_ctor_get_uint8(v_env_831_, sizeof(void*)*8);
lean_dec_ref(v_env_831_);
v___x_833_ = lean_st_ref_get(v___y_828_);
v_env_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc_ref(v_env_834_);
lean_dec(v___x_833_);
v___x_835_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2);
lean_inc(v_mod_824_);
v_entry_836_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_836_, 0, v_mod_824_);
lean_ctor_set_uint8(v_entry_836_, sizeof(void*)*1, v_isExporting_832_);
lean_ctor_set_uint8(v_entry_836_, sizeof(void*)*1 + 1, v_isMeta_825_);
v___x_837_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_838_ = lean_box(1);
v___x_839_ = lean_box(0);
v___x_867_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_835_, v___x_837_, v_env_834_, v___x_838_, v___x_839_);
v___x_868_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v___x_867_, v_entry_836_);
lean_dec(v___x_867_);
v___x_869_ = lean_bool_not(v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec_ref_known(v_entry_836_, 1);
lean_dec(v_hint_826_);
lean_dec(v_mod_824_);
v___x_870_ = lean_box(0);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_scopes_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v_opts_878_; uint8_t v_hasTrace_879_; 
v___x_872_ = l_Lean_inheritedTraceOptions;
v___x_873_ = lean_st_ref_get(v___x_872_);
v___x_874_ = lean_st_ref_get(v___y_828_);
v_scopes_875_ = lean_ctor_get(v___x_874_, 2);
lean_inc(v_scopes_875_);
lean_dec(v___x_874_);
v___x_876_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_877_ = l_List_head_x21___redArg(v___x_876_, v_scopes_875_);
lean_dec(v_scopes_875_);
v_opts_878_ = lean_ctor_get(v___x_877_, 1);
lean_inc_ref(v_opts_878_);
lean_dec(v___x_877_);
v_hasTrace_879_ = lean_ctor_get_uint8(v_opts_878_, sizeof(void*)*1);
if (v_hasTrace_879_ == 0)
{
lean_dec_ref(v_opts_878_);
lean_dec(v___x_873_);
lean_dec(v_hint_826_);
lean_dec(v_mod_824_);
v___y_841_ = v___y_828_;
goto v___jp_840_;
}
else
{
lean_object* v_cls_880_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___x_900_; uint8_t v___x_901_; 
v_cls_880_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4));
v___x_900_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12);
v___x_901_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_873_, v_opts_878_, v___x_900_);
lean_dec_ref(v_opts_878_);
lean_dec(v___x_873_);
if (v___x_901_ == 0)
{
lean_dec(v_hint_826_);
lean_dec(v_mod_824_);
v___y_841_ = v___y_828_;
goto v___jp_840_;
}
else
{
lean_object* v___x_902_; lean_object* v___y_904_; 
v___x_902_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14);
if (v_isExporting_832_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19));
v___y_904_ = v___x_911_;
goto v___jp_903_;
}
else
{
lean_object* v___x_912_; 
v___x_912_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20));
v___y_904_ = v___x_912_;
goto v___jp_903_;
}
v___jp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_inc_ref(v___y_904_);
v___x_905_ = l_Lean_stringToMessageData(v___y_904_);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_902_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
if (v_isMeta_825_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17));
v___y_887_ = v___x_908_;
v___y_888_ = v___x_909_;
goto v___jp_886_;
}
else
{
lean_object* v___x_910_; 
v___x_910_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18));
v___y_887_ = v___x_908_;
v___y_888_ = v___x_910_;
goto v___jp_886_;
}
}
}
v___jp_881_:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___y_882_);
lean_ctor_set(v___x_884_, 1, v___y_883_);
v___x_885_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_cls_880_, v___x_884_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_dec_ref_known(v___x_885_, 1);
v___y_841_ = v___y_828_;
goto v___jp_840_;
}
else
{
lean_dec_ref_known(v_entry_836_, 1);
return v___x_885_;
}
}
v___jp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
lean_inc_ref(v___y_888_);
v___x_889_ = l_Lean_stringToMessageData(v___y_888_);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___y_887_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Lean_MessageData_ofName(v_mod_824_);
v___x_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = l_Lean_Name_isAnonymous(v_hint_826_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8);
v___x_897_ = l_Lean_MessageData_ofName(v_hint_826_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___y_882_ = v___x_894_;
v___y_883_ = v___x_898_;
goto v___jp_881_;
}
else
{
lean_object* v___x_899_; 
lean_dec(v_hint_826_);
v___x_899_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9);
v___y_882_ = v___x_894_;
v___y_883_ = v___x_899_;
goto v___jp_881_;
}
}
}
}
v___jp_840_:
{
lean_object* v___x_842_; lean_object* v_toEnvExtension_843_; lean_object* v_env_844_; lean_object* v_messages_845_; lean_object* v_scopes_846_; lean_object* v_usedQuotCtxts_847_; lean_object* v_nextMacroScope_848_; lean_object* v_maxRecDepth_849_; lean_object* v_ngen_850_; lean_object* v_auxDeclNGen_851_; lean_object* v_infoState_852_; lean_object* v_traceState_853_; lean_object* v_snapshotTasks_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_866_; 
v___x_842_ = lean_st_ref_take(v___y_841_);
v_toEnvExtension_843_ = lean_ctor_get(v___x_837_, 0);
v_env_844_ = lean_ctor_get(v___x_842_, 0);
v_messages_845_ = lean_ctor_get(v___x_842_, 1);
v_scopes_846_ = lean_ctor_get(v___x_842_, 2);
v_usedQuotCtxts_847_ = lean_ctor_get(v___x_842_, 3);
v_nextMacroScope_848_ = lean_ctor_get(v___x_842_, 4);
v_maxRecDepth_849_ = lean_ctor_get(v___x_842_, 5);
v_ngen_850_ = lean_ctor_get(v___x_842_, 6);
v_auxDeclNGen_851_ = lean_ctor_get(v___x_842_, 7);
v_infoState_852_ = lean_ctor_get(v___x_842_, 8);
v_traceState_853_ = lean_ctor_get(v___x_842_, 9);
v_snapshotTasks_854_ = lean_ctor_get(v___x_842_, 10);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_866_ == 0)
{
v___x_856_ = v___x_842_;
v_isShared_857_ = v_isSharedCheck_866_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_snapshotTasks_854_);
lean_inc(v_traceState_853_);
lean_inc(v_infoState_852_);
lean_inc(v_auxDeclNGen_851_);
lean_inc(v_ngen_850_);
lean_inc(v_maxRecDepth_849_);
lean_inc(v_nextMacroScope_848_);
lean_inc(v_usedQuotCtxts_847_);
lean_inc(v_scopes_846_);
lean_inc(v_messages_845_);
lean_inc(v_env_844_);
lean_dec(v___x_842_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_866_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_asyncMode_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v_asyncMode_858_ = lean_ctor_get(v_toEnvExtension_843_, 2);
v___x_859_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_837_, v_env_844_, v_entry_836_, v_asyncMode_858_, v___x_839_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_859_);
v___x_861_ = v___x_856_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_messages_845_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_scopes_846_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_usedQuotCtxts_847_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_nextMacroScope_848_);
lean_ctor_set(v_reuseFailAlloc_865_, 5, v_maxRecDepth_849_);
lean_ctor_set(v_reuseFailAlloc_865_, 6, v_ngen_850_);
lean_ctor_set(v_reuseFailAlloc_865_, 7, v_auxDeclNGen_851_);
lean_ctor_set(v_reuseFailAlloc_865_, 8, v_infoState_852_);
lean_ctor_set(v_reuseFailAlloc_865_, 9, v_traceState_853_);
lean_ctor_set(v_reuseFailAlloc_865_, 10, v_snapshotTasks_854_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_st_ref_set(v___y_841_, v___x_861_);
v___x_863_ = lean_box(0);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___boxed(lean_object* v_mod_913_, lean_object* v_isMeta_914_, lean_object* v_hint_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
uint8_t v_isMeta_boxed_919_; lean_object* v_res_920_; 
v_isMeta_boxed_919_ = lean_unbox(v_isMeta_914_);
v_res_920_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_mod_913_, v_isMeta_boxed_919_, v_hint_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(lean_object* v___x_921_, lean_object* v_declName_922_, lean_object* v_as_923_, size_t v_sz_924_, size_t v_i_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_usize_dec_lt(v_i_925_, v_sz_924_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_dec(v_declName_922_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v_b_926_);
return v___x_931_;
}
else
{
lean_object* v___x_932_; lean_object* v_modules_933_; lean_object* v___x_934_; lean_object* v_a_935_; lean_object* v___x_936_; lean_object* v_toImport_937_; lean_object* v_module_938_; uint8_t v___x_939_; lean_object* v___x_940_; 
v___x_932_ = l_Lean_Environment_header(v___x_921_);
v_modules_933_ = lean_ctor_get(v___x_932_, 3);
lean_inc_ref(v_modules_933_);
lean_dec_ref(v___x_932_);
v___x_934_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_935_ = lean_array_uget_borrowed(v_as_923_, v_i_925_);
v___x_936_ = lean_array_get(v___x_934_, v_modules_933_, v_a_935_);
lean_dec_ref(v_modules_933_);
v_toImport_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc_ref(v_toImport_937_);
lean_dec(v___x_936_);
v_module_938_ = lean_ctor_get(v_toImport_937_, 0);
lean_inc(v_module_938_);
lean_dec_ref(v_toImport_937_);
v___x_939_ = 0;
lean_inc(v_declName_922_);
v___x_940_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_938_, v___x_939_, v_declName_922_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_941_; size_t v___x_942_; size_t v___x_943_; 
lean_dec_ref_known(v___x_940_, 1);
v___x_941_ = lean_box(0);
v___x_942_ = ((size_t)1ULL);
v___x_943_ = lean_usize_add(v_i_925_, v___x_942_);
v_i_925_ = v___x_943_;
v_b_926_ = v___x_941_;
goto _start;
}
else
{
lean_dec(v_declName_922_);
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___boxed(lean_object* v___x_945_, lean_object* v_declName_946_, lean_object* v_as_947_, lean_object* v_sz_948_, lean_object* v_i_949_, lean_object* v_b_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
size_t v_sz_boxed_954_; size_t v_i_boxed_955_; lean_object* v_res_956_; 
v_sz_boxed_954_ = lean_unbox_usize(v_sz_948_);
lean_dec(v_sz_948_);
v_i_boxed_955_ = lean_unbox_usize(v_i_949_);
lean_dec(v_i_949_);
v_res_956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v___x_945_, v_declName_946_, v_as_947_, v_sz_boxed_954_, v_i_boxed_955_, v_b_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec_ref(v_as_947_);
lean_dec_ref(v___x_945_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_a_957_, lean_object* v_x_958_){
_start:
{
if (lean_obj_tag(v_x_958_) == 0)
{
lean_object* v___x_959_; 
v___x_959_ = lean_box(0);
return v___x_959_;
}
else
{
lean_object* v_key_960_; lean_object* v_value_961_; lean_object* v_tail_962_; uint8_t v___x_963_; 
v_key_960_ = lean_ctor_get(v_x_958_, 0);
v_value_961_ = lean_ctor_get(v_x_958_, 1);
v_tail_962_ = lean_ctor_get(v_x_958_, 2);
v___x_963_ = lean_name_eq(v_key_960_, v_a_957_);
if (v___x_963_ == 0)
{
v_x_958_ = v_tail_962_;
goto _start;
}
else
{
lean_object* v___x_965_; 
lean_inc(v_value_961_);
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v_value_961_);
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_a_966_, lean_object* v_x_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_966_, v_x_967_);
lean_dec(v_x_967_);
lean_dec(v_a_966_);
return v_res_968_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_969_; uint64_t v___x_970_; 
v___x_969_ = lean_unsigned_to_nat(1723u);
v___x_970_ = lean_uint64_of_nat(v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(lean_object* v_m_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_buckets_973_; lean_object* v___x_974_; uint64_t v___y_976_; 
v_buckets_973_ = lean_ctor_get(v_m_971_, 1);
v___x_974_ = lean_array_get_size(v_buckets_973_);
if (lean_obj_tag(v_a_972_) == 0)
{
uint64_t v___x_990_; 
v___x_990_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0);
v___y_976_ = v___x_990_;
goto v___jp_975_;
}
else
{
uint64_t v_hash_991_; 
v_hash_991_ = lean_ctor_get_uint64(v_a_972_, sizeof(void*)*2);
v___y_976_ = v_hash_991_;
goto v___jp_975_;
}
v___jp_975_:
{
uint64_t v___x_977_; uint64_t v___x_978_; uint64_t v_fold_979_; uint64_t v___x_980_; uint64_t v___x_981_; uint64_t v___x_982_; size_t v___x_983_; size_t v___x_984_; size_t v___x_985_; size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_977_ = 32ULL;
v___x_978_ = lean_uint64_shift_right(v___y_976_, v___x_977_);
v_fold_979_ = lean_uint64_xor(v___y_976_, v___x_978_);
v___x_980_ = 16ULL;
v___x_981_ = lean_uint64_shift_right(v_fold_979_, v___x_980_);
v___x_982_ = lean_uint64_xor(v_fold_979_, v___x_981_);
v___x_983_ = lean_uint64_to_usize(v___x_982_);
v___x_984_ = lean_usize_of_nat(v___x_974_);
v___x_985_ = ((size_t)1ULL);
v___x_986_ = lean_usize_sub(v___x_984_, v___x_985_);
v___x_987_ = lean_usize_land(v___x_983_, v___x_986_);
v___x_988_ = lean_array_uget_borrowed(v_buckets_973_, v___x_987_);
v___x_989_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_972_, v___x_988_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_m_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_992_, v_a_993_);
lean_dec(v_a_993_);
lean_dec_ref(v_m_992_);
return v_res_994_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1));
v___x_998_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0));
v___x_999_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_998_, v___x_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(lean_object* v_declName_1002_, uint8_t v_isMeta_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v_env_1011_; lean_object* v___y_1013_; lean_object* v___x_1026_; 
v___x_1007_ = lean_st_ref_get(v___y_1005_);
v_env_1011_ = lean_ctor_get(v___x_1007_, 0);
lean_inc_ref(v_env_1011_);
lean_dec(v___x_1007_);
v___x_1026_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1011_, v_declName_1002_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_dec_ref(v_env_1011_);
lean_dec(v_declName_1002_);
goto v___jp_1008_;
}
else
{
lean_object* v_val_1027_; lean_object* v___x_1028_; lean_object* v_modules_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v_val_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_val_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = l_Lean_Environment_header(v_env_1011_);
v_modules_1029_ = lean_ctor_get(v___x_1028_, 3);
lean_inc_ref(v_modules_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = lean_array_get_size(v_modules_1029_);
v___x_1031_ = lean_nat_dec_lt(v_val_1027_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_dec_ref(v_modules_1029_);
lean_dec(v_val_1027_);
lean_dec_ref(v_env_1011_);
lean_dec(v_declName_1002_);
goto v___jp_1008_;
}
else
{
lean_object* v___x_1032_; lean_object* v_env_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___y_1037_; 
v___x_1032_ = lean_st_ref_get(v___y_1005_);
v_env_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc_ref(v_env_1033_);
lean_dec(v___x_1032_);
v___x_1034_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2);
v___x_1035_ = lean_array_fget(v_modules_1029_, v_val_1027_);
lean_dec(v_val_1027_);
lean_dec_ref(v_modules_1029_);
if (v_isMeta_1003_ == 0)
{
lean_dec_ref(v_env_1033_);
v___y_1037_ = v_isMeta_1003_;
goto v___jp_1036_;
}
else
{
uint8_t v___x_1048_; uint8_t v___x_1049_; 
lean_inc(v_declName_1002_);
v___x_1048_ = l_Lean_isMarkedMeta(v_env_1033_, v_declName_1002_);
v___x_1049_ = lean_bool_not(v___x_1048_);
v___y_1037_ = v___x_1049_;
goto v___jp_1036_;
}
v___jp_1036_:
{
lean_object* v_toImport_1038_; lean_object* v_module_1039_; lean_object* v___x_1040_; 
v_toImport_1038_ = lean_ctor_get(v___x_1035_, 0);
lean_inc_ref(v_toImport_1038_);
lean_dec(v___x_1035_);
v_module_1039_ = lean_ctor_get(v_toImport_1038_, 0);
lean_inc(v_module_1039_);
lean_dec_ref(v_toImport_1038_);
lean_inc(v_declName_1002_);
v___x_1040_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_1039_, v___y_1037_, v_declName_1002_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec_ref_known(v___x_1040_, 1);
v___x_1041_ = l_Lean_indirectModUseExt;
v___x_1042_ = lean_box(1);
v___x_1043_ = lean_box(0);
lean_inc_ref(v_env_1011_);
v___x_1044_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1034_, v___x_1041_, v_env_1011_, v___x_1042_, v___x_1043_);
v___x_1045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v___x_1044_, v_declName_1002_);
lean_dec(v___x_1044_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3));
v___y_1013_ = v___x_1046_;
goto v___jp_1012_;
}
else
{
lean_object* v_val_1047_; 
v_val_1047_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_val_1047_);
lean_dec_ref_known(v___x_1045_, 1);
v___y_1013_ = v_val_1047_;
goto v___jp_1012_;
}
}
else
{
lean_dec_ref(v_env_1011_);
lean_dec(v_declName_1002_);
return v___x_1040_;
}
}
}
}
v___jp_1008_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
v___jp_1012_:
{
lean_object* v___x_1014_; size_t v_sz_1015_; size_t v___x_1016_; lean_object* v___x_1017_; 
v___x_1014_ = lean_box(0);
v_sz_1015_ = lean_array_size(v___y_1013_);
v___x_1016_ = ((size_t)0ULL);
v___x_1017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v_env_1011_, v_declName_1002_, v___y_1013_, v_sz_1015_, v___x_1016_, v___x_1014_, v___y_1004_, v___y_1005_);
lean_dec_ref(v___y_1013_);
lean_dec_ref(v_env_1011_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v___x_1017_, 0);
lean_dec(v_unused_1025_);
v___x_1019_ = v___x_1017_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_dec(v___x_1017_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1014_);
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1014_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
else
{
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___boxed(lean_object* v_declName_1050_, lean_object* v_isMeta_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v_isMeta_boxed_1055_; lean_object* v_res_1056_; 
v_isMeta_boxed_1055_ = lean_unbox(v_isMeta_1051_);
v_res_1056_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_declName_1050_, v_isMeta_boxed_1055_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(lean_object* v_as_x27_1057_, lean_object* v_b_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
if (lean_obj_tag(v_as_x27_1057_) == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_b_1058_);
return v___x_1062_;
}
else
{
lean_object* v_head_1063_; lean_object* v_tail_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; 
v_head_1063_ = lean_ctor_get(v_as_x27_1057_, 0);
v_tail_1064_ = lean_ctor_get(v_as_x27_1057_, 1);
v___x_1065_ = 1;
lean_inc(v_head_1063_);
v___x_1066_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_head_1063_, v___x_1065_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v___x_1067_; 
lean_dec_ref_known(v___x_1066_, 1);
v___x_1067_ = lean_box(0);
v_as_x27_1057_ = v_tail_1064_;
v_b_1058_ = v___x_1067_;
goto _start;
}
else
{
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg___boxed(lean_object* v_as_x27_1069_, lean_object* v_b_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_1069_, v_b_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_as_x27_1069_);
return v_res_1074_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(lean_object* v_opts_1075_, lean_object* v_opt_1076_){
_start:
{
lean_object* v_name_1077_; lean_object* v_defValue_1078_; lean_object* v_map_1079_; lean_object* v___x_1080_; 
v_name_1077_ = lean_ctor_get(v_opt_1076_, 0);
v_defValue_1078_ = lean_ctor_get(v_opt_1076_, 1);
v_map_1079_ = lean_ctor_get(v_opts_1075_, 0);
v___x_1080_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1079_, v_name_1077_);
if (lean_obj_tag(v___x_1080_) == 0)
{
uint8_t v___x_1081_; 
v___x_1081_ = lean_unbox(v_defValue_1078_);
return v___x_1081_;
}
else
{
lean_object* v_val_1082_; 
v_val_1082_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_val_1082_);
lean_dec_ref_known(v___x_1080_, 1);
if (lean_obj_tag(v_val_1082_) == 1)
{
uint8_t v_v_1083_; 
v_v_1083_ = lean_ctor_get_uint8(v_val_1082_, 0);
lean_dec_ref_known(v_val_1082_, 0);
return v_v_1083_;
}
else
{
uint8_t v___x_1084_; 
lean_dec(v_val_1082_);
v___x_1084_ = lean_unbox(v_defValue_1078_);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18___boxed(lean_object* v_opts_1085_, lean_object* v_opt_1086_){
_start:
{
uint8_t v_res_1087_; lean_object* v_r_1088_; 
v_res_1087_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(v_opts_1085_, v_opt_1086_);
lean_dec_ref(v_opt_1086_);
lean_dec_ref(v_opts_1085_);
v_r_1088_ = lean_box(v_res_1087_);
return v_r_1088_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_box(1);
v___x_1090_ = l_Lean_MessageData_ofFormat(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2));
v___x_1095_ = l_Lean_MessageData_ofFormat(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
return v_x_1096_;
}
else
{
lean_object* v_head_1098_; lean_object* v_tail_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1121_; 
v_head_1098_ = lean_ctor_get(v_x_1097_, 0);
v_tail_1099_ = lean_ctor_get(v_x_1097_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1101_ = v_x_1097_;
v_isShared_1102_ = v_isSharedCheck_1121_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_tail_1099_);
lean_inc(v_head_1098_);
lean_dec(v_x_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1121_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_before_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1119_; 
v_before_1103_ = lean_ctor_get(v_head_1098_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_head_1098_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v_head_1098_, 1);
lean_dec(v_unused_1120_);
v___x_1105_ = v_head_1098_;
v_isShared_1106_ = v_isSharedCheck_1119_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_before_1103_);
lean_dec(v_head_1098_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1119_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1107_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0);
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 7);
lean_ctor_set(v___x_1105_, 1, v___x_1107_);
lean_ctor_set(v___x_1105_, 0, v_x_1096_);
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_x_1096_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1110_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3);
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 7);
lean_ctor_set(v___x_1101_, 1, v___x_1110_);
lean_ctor_set(v___x_1101_, 0, v___x_1109_);
v___x_1112_ = v___x_1101_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = l_Lean_MessageData_ofSyntax(v_before_1103_);
v___x_1114_ = l_Lean_indentD(v___x_1113_);
v___x_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1112_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v_x_1096_ = v___x_1115_;
v_x_1097_ = v_tail_1099_;
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
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1));
v___x_1126_ = l_Lean_MessageData_ofFormat(v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(lean_object* v_msgData_1127_, lean_object* v_macroStack_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v_scopes_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_opts_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; uint8_t v___x_1138_; 
v___x_1131_ = lean_st_ref_get(v___y_1129_);
v_scopes_1132_ = lean_ctor_get(v___x_1131_, 2);
lean_inc(v_scopes_1132_);
lean_dec(v___x_1131_);
v___x_1133_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1134_ = l_List_head_x21___redArg(v___x_1133_, v_scopes_1132_);
lean_dec(v_scopes_1132_);
v_opts_1135_ = lean_ctor_get(v___x_1134_, 1);
lean_inc_ref(v_opts_1135_);
lean_dec(v___x_1134_);
v___x_1136_ = l_Lean_Elab_pp_macroStack;
v___x_1137_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(v_opts_1135_, v___x_1136_);
lean_dec_ref(v_opts_1135_);
v___x_1138_ = lean_bool_not(v___x_1137_);
if (v___x_1138_ == 0)
{
if (lean_obj_tag(v_macroStack_1128_) == 0)
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_msgData_1127_);
return v___x_1139_;
}
else
{
lean_object* v_head_1140_; lean_object* v_after_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1156_; 
v_head_1140_ = lean_ctor_get(v_macroStack_1128_, 0);
lean_inc(v_head_1140_);
v_after_1141_ = lean_ctor_get(v_head_1140_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_head_1140_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v_head_1140_, 0);
lean_dec(v_unused_1157_);
v___x_1143_ = v_head_1140_;
v_isShared_1144_ = v_isSharedCheck_1156_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_after_1141_);
lean_dec(v_head_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1156_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0);
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 7);
lean_ctor_set(v___x_1143_, 1, v___x_1145_);
lean_ctor_set(v___x_1143_, 0, v_msgData_1127_);
v___x_1147_ = v___x_1143_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_msgData_1127_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_msgData_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1148_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_MessageData_ofSyntax(v_after_1141_);
v___x_1151_ = l_Lean_indentD(v___x_1150_);
v_msgData_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1152_, 0, v___x_1149_);
lean_ctor_set(v_msgData_1152_, 1, v___x_1151_);
v___x_1153_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(v_msgData_1152_, v_macroStack_1128_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
}
}
else
{
lean_object* v___x_1158_; 
lean_dec(v_macroStack_1128_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_msgData_1127_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___boxed(lean_object* v_msgData_1159_, lean_object* v_macroStack_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_1159_, v_macroStack_1160_, v___y_1161_);
lean_dec(v___y_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(lean_object* v_msg_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Elab_Command_getRef___redArg(v___y_1165_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v_macroStack_1170_; lean_object* v___x_1171_; lean_object* v_a_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v_macroStack_1170_ = lean_ctor_get(v___y_1165_, 4);
v___x_1171_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_1164_, v___y_1166_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref(v___x_1171_);
v___x_1173_ = l_Lean_Elab_getBetterRef(v_a_1169_, v_macroStack_1170_);
lean_dec(v_a_1169_);
lean_inc(v_macroStack_1170_);
v___x_1174_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_a_1172_, v_macroStack_1170_, v___y_1166_);
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1173_);
lean_ctor_set(v___x_1179_, 1, v_a_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 1);
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v_msg_1164_);
v_a_1184_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1168_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1168_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg___boxed(lean_object* v_msg_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(lean_object* v_ref_1197_, lean_object* v_msg_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Elab_Command_getRef___redArg(v___y_1199_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v_fileName_1204_; lean_object* v_fileMap_1205_; lean_object* v_currRecDepth_1206_; lean_object* v_cmdPos_1207_; lean_object* v_macroStack_1208_; lean_object* v_quotContext_x3f_1209_; lean_object* v_currMacroScope_1210_; lean_object* v_snap_x3f_1211_; lean_object* v_cancelTk_x3f_1212_; uint8_t v_suppressElabErrors_1213_; lean_object* v_ref_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v_fileName_1204_ = lean_ctor_get(v___y_1199_, 0);
v_fileMap_1205_ = lean_ctor_get(v___y_1199_, 1);
v_currRecDepth_1206_ = lean_ctor_get(v___y_1199_, 2);
v_cmdPos_1207_ = lean_ctor_get(v___y_1199_, 3);
v_macroStack_1208_ = lean_ctor_get(v___y_1199_, 4);
v_quotContext_x3f_1209_ = lean_ctor_get(v___y_1199_, 5);
v_currMacroScope_1210_ = lean_ctor_get(v___y_1199_, 6);
v_snap_x3f_1211_ = lean_ctor_get(v___y_1199_, 8);
v_cancelTk_x3f_1212_ = lean_ctor_get(v___y_1199_, 9);
v_suppressElabErrors_1213_ = lean_ctor_get_uint8(v___y_1199_, sizeof(void*)*10);
v_ref_1214_ = l_Lean_replaceRef(v_ref_1197_, v_a_1203_);
lean_dec(v_a_1203_);
lean_inc(v_cancelTk_x3f_1212_);
lean_inc(v_snap_x3f_1211_);
lean_inc(v_currMacroScope_1210_);
lean_inc(v_quotContext_x3f_1209_);
lean_inc(v_macroStack_1208_);
lean_inc(v_cmdPos_1207_);
lean_inc(v_currRecDepth_1206_);
lean_inc_ref(v_fileMap_1205_);
lean_inc_ref(v_fileName_1204_);
v___x_1215_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1215_, 0, v_fileName_1204_);
lean_ctor_set(v___x_1215_, 1, v_fileMap_1205_);
lean_ctor_set(v___x_1215_, 2, v_currRecDepth_1206_);
lean_ctor_set(v___x_1215_, 3, v_cmdPos_1207_);
lean_ctor_set(v___x_1215_, 4, v_macroStack_1208_);
lean_ctor_set(v___x_1215_, 5, v_quotContext_x3f_1209_);
lean_ctor_set(v___x_1215_, 6, v_currMacroScope_1210_);
lean_ctor_set(v___x_1215_, 7, v_ref_1214_);
lean_ctor_set(v___x_1215_, 8, v_snap_x3f_1211_);
lean_ctor_set(v___x_1215_, 9, v_cancelTk_x3f_1212_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*10, v_suppressElabErrors_1213_);
v___x_1216_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1198_, v___x_1215_, v___y_1200_);
lean_dec_ref_known(v___x_1215_, 10);
return v___x_1216_;
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v_msg_1198_);
v_a_1217_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1202_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1202_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1225_, lean_object* v_msg_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_1225_, v_msg_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v_ref_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(lean_object* v_env_1231_, lean_object* v_declName_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v___x_1235_; lean_object* v_env_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; uint8_t v___x_1239_; 
v___x_1235_ = 0;
v_env_1236_ = l_Lean_Environment_setExporting(v_env_1231_, v___x_1235_);
lean_inc(v_declName_1232_);
v___x_1237_ = l_Lean_mkPrivateName(v_env_1236_, v_declName_1232_);
v___x_1238_ = 1;
lean_inc_ref(v_env_1236_);
v___x_1239_ = l_Lean_Environment_contains(v_env_1236_, v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1240_ = l_Lean_privateToUserName(v_declName_1232_);
v___x_1241_ = l_Lean_Environment_contains(v_env_1236_, v___x_1240_, v___x_1238_);
v___x_1242_ = lean_box(v___x_1241_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v___y_1234_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v_env_1236_);
lean_dec(v_declName_1232_);
v___x_1244_ = lean_box(v___x_1239_);
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v___y_1234_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed(lean_object* v_env_1246_, lean_object* v_declName_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(v_env_1246_, v_declName_1247_, v___y_1248_, v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(lean_object* v_as_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
if (lean_obj_tag(v_as_1251_) == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_box(0);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
else
{
lean_object* v_head_1257_; lean_object* v_tail_1258_; lean_object* v_fst_1259_; lean_object* v_snd_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_scopes_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_opts_1267_; uint8_t v_hasTrace_1268_; 
v_head_1257_ = lean_ctor_get(v_as_1251_, 0);
lean_inc(v_head_1257_);
v_tail_1258_ = lean_ctor_get(v_as_1251_, 1);
lean_inc(v_tail_1258_);
lean_dec_ref_known(v_as_1251_, 2);
v_fst_1259_ = lean_ctor_get(v_head_1257_, 0);
lean_inc(v_fst_1259_);
v_snd_1260_ = lean_ctor_get(v_head_1257_, 1);
lean_inc(v_snd_1260_);
lean_dec(v_head_1257_);
v___x_1261_ = l_Lean_inheritedTraceOptions;
v___x_1262_ = lean_st_ref_get(v___x_1261_);
v___x_1263_ = lean_st_ref_get(v___y_1253_);
v_scopes_1264_ = lean_ctor_get(v___x_1263_, 2);
lean_inc(v_scopes_1264_);
lean_dec(v___x_1263_);
v___x_1265_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1266_ = l_List_head_x21___redArg(v___x_1265_, v_scopes_1264_);
lean_dec(v_scopes_1264_);
v_opts_1267_ = lean_ctor_get(v___x_1266_, 1);
lean_inc_ref(v_opts_1267_);
lean_dec(v___x_1266_);
v_hasTrace_1268_ = lean_ctor_get_uint8(v_opts_1267_, sizeof(void*)*1);
if (v_hasTrace_1268_ == 0)
{
lean_dec_ref(v_opts_1267_);
lean_dec(v___x_1262_);
lean_dec(v_snd_1260_);
lean_dec(v_fst_1259_);
v_as_1251_ = v_tail_1258_;
goto _start;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1270_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11));
lean_inc(v_fst_1259_);
v___x_1271_ = l_Lean_Name_append(v___x_1270_, v_fst_1259_);
v___x_1272_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1262_, v_opts_1267_, v___x_1271_);
lean_dec(v___x_1271_);
lean_dec_ref(v_opts_1267_);
lean_dec(v___x_1262_);
if (v___x_1272_ == 0)
{
lean_dec(v_snd_1260_);
lean_dec(v_fst_1259_);
v_as_1251_ = v_tail_1258_;
goto _start;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_snd_1260_);
v___x_1275_ = l_Lean_MessageData_ofFormat(v___x_1274_);
v___x_1276_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_fst_1259_, v___x_1275_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_dec_ref_known(v___x_1276_, 1);
v_as_1251_ = v_tail_1258_;
goto _start;
}
else
{
lean_dec(v_tail_1258_);
return v___x_1276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3___boxed(lean_object* v_as_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v_as_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(lean_object* v_env_1283_, lean_object* v_opts_1284_, lean_object* v_currNamespace_1285_, lean_object* v_openDecls_1286_, lean_object* v_n_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = l_Lean_ResolveName_resolveGlobalName(v_env_1283_, v_opts_1284_, v_currNamespace_1285_, v_openDecls_1286_, v_n_1287_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___y_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed(lean_object* v_env_1292_, lean_object* v_opts_1293_, lean_object* v_currNamespace_1294_, lean_object* v_openDecls_1295_, lean_object* v_n_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(v_env_1292_, v_opts_1293_, v_currNamespace_1294_, v_openDecls_1295_, v_n_1296_, v___y_1297_, v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec_ref(v_opts_1293_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(lean_object* v_x_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v_env_1306_; lean_object* v___x_1307_; lean_object* v_scopes_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v_opts_1311_; lean_object* v___x_1312_; 
v___x_1305_ = lean_st_ref_get(v___y_1303_);
v_env_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_env_1306_);
lean_dec(v___x_1305_);
v___x_1307_ = lean_st_ref_get(v___y_1303_);
v_scopes_1308_ = lean_ctor_get(v___x_1307_, 2);
lean_inc(v_scopes_1308_);
lean_dec(v___x_1307_);
v___x_1309_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1310_ = l_List_head_x21___redArg(v___x_1309_, v_scopes_1308_);
lean_dec(v_scopes_1308_);
v_opts_1311_ = lean_ctor_get(v___x_1310_, 1);
lean_inc_ref(v_opts_1311_);
lean_dec(v___x_1310_);
v___x_1312_ = l_Lean_Elab_Command_getScope___redArg(v___y_1303_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v_currNamespace_1314_; lean_object* v___x_1315_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v_currNamespace_1314_ = lean_ctor_get(v_a_1313_, 2);
lean_inc(v_currNamespace_1314_);
lean_dec(v_a_1313_);
v___x_1315_ = l_Lean_Elab_Command_getScope___redArg(v___y_1303_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v_openDecls_1317_; lean_object* v___x_1318_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v_openDecls_1317_ = lean_ctor_get(v_a_1316_, 3);
lean_inc(v_openDecls_1317_);
lean_dec(v_a_1316_);
v___x_1318_ = l_Lean_Elab_Command_getRef___redArg(v___y_1302_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1302_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v_currRecDepth_1322_; lean_object* v_quotContext_x3f_1323_; lean_object* v___f_1324_; lean_object* v___f_1325_; lean_object* v___f_1326_; lean_object* v___f_1327_; lean_object* v___f_1328_; lean_object* v_methods_1329_; lean_object* v_a_1331_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1320_, 1);
v_currRecDepth_1322_ = lean_ctor_get(v___y_1302_, 2);
v_quotContext_x3f_1323_ = lean_ctor_get(v___y_1302_, 5);
lean_inc_ref_n(v_env_1306_, 3);
v___f_1324_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1324_, 0, v_env_1306_);
v___f_1325_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1325_, 0, v_env_1306_);
lean_inc_n(v_currNamespace_1314_, 2);
v___f_1326_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1326_, 0, v_currNamespace_1314_);
lean_inc(v_openDecls_1317_);
v___f_1327_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1327_, 0, v_env_1306_);
lean_closure_set(v___f_1327_, 1, v_currNamespace_1314_);
lean_closure_set(v___f_1327_, 2, v_openDecls_1317_);
v___f_1328_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1328_, 0, v_env_1306_);
lean_closure_set(v___f_1328_, 1, v_opts_1311_);
lean_closure_set(v___f_1328_, 2, v_currNamespace_1314_);
lean_closure_set(v___f_1328_, 3, v_openDecls_1317_);
v_methods_1329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1329_, 0, v___f_1325_);
lean_ctor_set(v_methods_1329_, 1, v___f_1326_);
lean_ctor_set(v_methods_1329_, 2, v___f_1324_);
lean_ctor_set(v_methods_1329_, 3, v___f_1327_);
lean_ctor_set(v_methods_1329_, 4, v___f_1328_);
if (lean_obj_tag(v_quotContext_x3f_1323_) == 0)
{
lean_object* v___x_1403_; lean_object* v_a_1404_; 
v___x_1403_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_1303_);
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref(v___x_1403_);
v_a_1331_ = v_a_1404_;
goto v___jp_1330_;
}
else
{
lean_object* v_val_1405_; 
v_val_1405_ = lean_ctor_get(v_quotContext_x3f_1323_, 0);
lean_inc(v_val_1405_);
v_a_1331_ = v_val_1405_;
goto v___jp_1330_;
}
v___jp_1330_:
{
lean_object* v___x_1332_; lean_object* v_maxRecDepth_1333_; lean_object* v___x_1334_; lean_object* v_nextMacroScope_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1332_ = lean_st_ref_get(v___y_1303_);
v_maxRecDepth_1333_ = lean_ctor_get(v___x_1332_, 5);
lean_inc(v_maxRecDepth_1333_);
lean_dec(v___x_1332_);
v___x_1334_ = lean_st_ref_get(v___y_1303_);
v_nextMacroScope_1335_ = lean_ctor_get(v___x_1334_, 4);
lean_inc(v_nextMacroScope_1335_);
lean_dec(v___x_1334_);
lean_inc(v_currRecDepth_1322_);
v___x_1336_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1336_, 0, v_methods_1329_);
lean_ctor_set(v___x_1336_, 1, v_a_1331_);
lean_ctor_set(v___x_1336_, 2, v_a_1321_);
lean_ctor_set(v___x_1336_, 3, v_currRecDepth_1322_);
lean_ctor_set(v___x_1336_, 4, v_maxRecDepth_1333_);
lean_ctor_set(v___x_1336_, 5, v_a_1319_);
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1338_, 0, v_nextMacroScope_1335_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
lean_ctor_set(v___x_1338_, 2, v___x_1337_);
v___x_1339_ = lean_apply_2(v_x_1301_, v___x_1336_, v___x_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v_a_1341_; lean_object* v_macroScope_1342_; lean_object* v_traceMsgs_1343_; lean_object* v_expandedMacroDecls_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 1);
lean_inc(v_a_1340_);
v_a_1341_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1339_, 2);
v_macroScope_1342_ = lean_ctor_get(v_a_1340_, 0);
lean_inc(v_macroScope_1342_);
v_traceMsgs_1343_ = lean_ctor_get(v_a_1340_, 1);
lean_inc(v_traceMsgs_1343_);
v_expandedMacroDecls_1344_ = lean_ctor_get(v_a_1340_, 2);
lean_inc(v_expandedMacroDecls_1344_);
lean_dec(v_a_1340_);
v___x_1345_ = lean_box(0);
v___x_1346_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_expandedMacroDecls_1344_, v___x_1345_, v___y_1302_, v___y_1303_);
lean_dec(v_expandedMacroDecls_1344_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v___x_1347_; lean_object* v_env_1348_; lean_object* v_messages_1349_; lean_object* v_scopes_1350_; lean_object* v_usedQuotCtxts_1351_; lean_object* v_maxRecDepth_1352_; lean_object* v_ngen_1353_; lean_object* v_auxDeclNGen_1354_; lean_object* v_infoState_1355_; lean_object* v_traceState_1356_; lean_object* v_snapshotTasks_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref_known(v___x_1346_, 1);
v___x_1347_ = lean_st_ref_take(v___y_1303_);
v_env_1348_ = lean_ctor_get(v___x_1347_, 0);
v_messages_1349_ = lean_ctor_get(v___x_1347_, 1);
v_scopes_1350_ = lean_ctor_get(v___x_1347_, 2);
v_usedQuotCtxts_1351_ = lean_ctor_get(v___x_1347_, 3);
v_maxRecDepth_1352_ = lean_ctor_get(v___x_1347_, 5);
v_ngen_1353_ = lean_ctor_get(v___x_1347_, 6);
v_auxDeclNGen_1354_ = lean_ctor_get(v___x_1347_, 7);
v_infoState_1355_ = lean_ctor_get(v___x_1347_, 8);
v_traceState_1356_ = lean_ctor_get(v___x_1347_, 9);
v_snapshotTasks_1357_ = lean_ctor_get(v___x_1347_, 10);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; 
v_unused_1384_ = lean_ctor_get(v___x_1347_, 4);
lean_dec(v_unused_1384_);
v___x_1359_ = v___x_1347_;
v_isShared_1360_ = v_isSharedCheck_1383_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_snapshotTasks_1357_);
lean_inc(v_traceState_1356_);
lean_inc(v_infoState_1355_);
lean_inc(v_auxDeclNGen_1354_);
lean_inc(v_ngen_1353_);
lean_inc(v_maxRecDepth_1352_);
lean_inc(v_usedQuotCtxts_1351_);
lean_inc(v_scopes_1350_);
lean_inc(v_messages_1349_);
lean_inc(v_env_1348_);
lean_dec(v___x_1347_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1383_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 4, v_macroScope_1342_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_env_1348_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_messages_1349_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_scopes_1350_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_usedQuotCtxts_1351_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v_macroScope_1342_);
lean_ctor_set(v_reuseFailAlloc_1382_, 5, v_maxRecDepth_1352_);
lean_ctor_set(v_reuseFailAlloc_1382_, 6, v_ngen_1353_);
lean_ctor_set(v_reuseFailAlloc_1382_, 7, v_auxDeclNGen_1354_);
lean_ctor_set(v_reuseFailAlloc_1382_, 8, v_infoState_1355_);
lean_ctor_set(v_reuseFailAlloc_1382_, 9, v_traceState_1356_);
lean_ctor_set(v_reuseFailAlloc_1382_, 10, v_snapshotTasks_1357_);
v___x_1362_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_st_ref_set(v___y_1303_, v___x_1362_);
v___x_1364_ = l_List_reverse___redArg(v_traceMsgs_1343_);
v___x_1365_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v___x_1364_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v___x_1365_, 0);
lean_dec(v_unused_1373_);
v___x_1367_ = v___x_1365_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_dec(v___x_1365_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v_a_1341_);
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1341_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_a_1341_);
v_a_1374_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1365_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1365_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_traceMsgs_1343_);
lean_dec(v_macroScope_1342_);
lean_dec(v_a_1341_);
v_a_1385_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1346_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1346_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v_a_1393_; 
v_a_1393_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1339_, 2);
if (lean_obj_tag(v_a_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v_a_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v_a_1394_ = lean_ctor_get(v_a_1393_, 0);
lean_inc(v_a_1394_);
v_a_1395_ = lean_ctor_get(v_a_1393_, 1);
lean_inc_ref(v_a_1395_);
lean_dec_ref_known(v_a_1393_, 2);
v___x_1396_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0));
v___x_1397_ = lean_string_dec_eq(v_a_1395_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_a_1395_);
v___x_1399_ = l_Lean_MessageData_ofFormat(v___x_1398_);
v___x_1400_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_a_1394_, v___x_1399_, v___y_1302_, v___y_1303_);
lean_dec(v_a_1394_);
return v___x_1400_;
}
else
{
lean_object* v___x_1401_; 
lean_dec_ref(v_a_1395_);
v___x_1401_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_a_1394_);
return v___x_1401_;
}
}
else
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v___x_1402_;
}
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec(v_a_1319_);
lean_dec(v_openDecls_1317_);
lean_dec(v_currNamespace_1314_);
lean_dec_ref(v_opts_1311_);
lean_dec_ref(v_env_1306_);
lean_dec_ref(v_x_1301_);
v_a_1406_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1320_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1320_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_openDecls_1317_);
lean_dec(v_currNamespace_1314_);
lean_dec_ref(v_opts_1311_);
lean_dec_ref(v_env_1306_);
lean_dec_ref(v_x_1301_);
v_a_1414_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1318_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1318_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v_currNamespace_1314_);
lean_dec_ref(v_opts_1311_);
lean_dec_ref(v_env_1306_);
lean_dec_ref(v_x_1301_);
v_a_1422_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1315_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1315_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v_opts_1311_);
lean_dec_ref(v_env_1306_);
lean_dec_ref(v_x_1301_);
v_a_1430_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1312_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1312_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___boxed(lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v_x_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1442_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1458_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11));
v___x_1459_ = l_Lean_Name_append(v___x_1458_, v___x_1457_);
return v___x_1459_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__8));
v___x_1462_ = l_Lean_stringToMessageData(v___x_1461_);
return v___x_1462_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__10));
v___x_1465_ = l_Lean_stringToMessageData(v___x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object* v_modifiers_1466_, lean_object* v_stx_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v___x_1471_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v_declId_1478_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1491_ = l_Lean_Syntax_getArg(v_stx_1467_, v___x_1471_);
v___x_1492_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_1492_, 0, v___x_1491_);
v___x_1493_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_1492_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v___x_1495_ = lean_unsigned_to_nat(2u);
v___x_1518_ = l_Lean_Syntax_getArg(v_stx_1467_, v___x_1495_);
v___x_1519_ = lean_alloc_closure((void*)(l_Lean_Elab_expandOptNamedPrio___boxed), 3, 1);
lean_closure_set(v___x_1519_, 0, v___x_1518_);
v___x_1520_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_1519_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1522_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v___x_1522_ = l_Lean_Elab_Command_getRef___redArg(v_a_1468_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1468_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_quotContext_x3f_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; 
lean_dec_ref_known(v___x_1524_, 1);
v_quotContext_x3f_1525_ = lean_ctor_get(v_a_1468_, 5);
v___x_1526_ = 0;
v___x_1527_ = l_Lean_SourceInfo_fromRef(v_a_1523_, v___x_1526_);
lean_dec(v_a_1523_);
if (lean_obj_tag(v_quotContext_x3f_1525_) == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1469_);
lean_dec_ref(v___x_1662_);
goto v___jp_1528_;
}
else
{
goto v___jp_1528_;
}
v___jp_1528_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_fst_1532_; lean_object* v_snd_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1661_; 
v___x_1529_ = lean_unsigned_to_nat(4u);
v___x_1530_ = l_Lean_Syntax_getArg(v_stx_1467_, v___x_1529_);
v___x_1531_ = l_Lean_Elab_expandDeclSig(v___x_1530_);
lean_dec(v___x_1530_);
v_fst_1532_ = lean_ctor_get(v___x_1531_, 0);
v_snd_1533_ = lean_ctor_get(v___x_1531_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1535_ = v___x_1531_;
v_isShared_1536_ = v_isSharedCheck_1661_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_snd_1533_);
lean_inc(v_fst_1532_);
lean_dec(v___x_1531_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1661_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1537_ = ((lean_object*)(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_));
v___x_1538_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2));
v___x_1539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0));
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4));
lean_inc(v___x_1527_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set_tag(v___x_1535_, 2);
lean_ctor_set(v___x_1535_, 1, v___x_1539_);
lean_ctor_set(v___x_1535_, 0, v___x_1527_);
v___x_1542_ = v___x_1535_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v___x_1539_);
v___x_1542_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1543_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1544_ = l_Nat_reprFast(v_a_1521_);
v___x_1545_ = lean_box(2);
v___x_1546_ = l_Lean_Syntax_mkNumLit(v___x_1544_, v___x_1545_);
lean_inc(v___x_1527_);
v___x_1547_ = l_Lean_Syntax_node1(v___x_1527_, v___x_1543_, v___x_1546_);
v___x_1548_ = l_Lean_Syntax_node2(v___x_1527_, v___x_1540_, v___x_1542_, v___x_1547_);
v___x_1549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1));
v___x_1550_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1548_);
v___x_1551_ = lean_unbox(v_a_1494_);
lean_dec(v_a_1494_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*2, v___x_1551_);
v___x_1552_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_1466_, v___x_1550_);
v___x_1553_ = lean_unsigned_to_nat(3u);
v___x_1554_ = l_Lean_Syntax_getArg(v_stx_1467_, v___x_1553_);
v___x_1555_ = l_Lean_Syntax_getOptional_x3f(v___x_1554_);
lean_dec(v___x_1554_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = l_Lean_Syntax_getArgs(v_fst_1532_);
lean_inc(v_snd_1533_);
v___x_1557_ = l_Lean_Elab_Command_mkInstanceName(v___x_1556_, v_snd_1533_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v_scopes_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_opts_1565_; uint8_t v_hasTrace_1566_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = l_Lean_inheritedTraceOptions;
v___x_1560_ = lean_st_ref_get(v___x_1559_);
v___x_1561_ = lean_st_ref_get(v_a_1469_);
v_scopes_1562_ = lean_ctor_get(v___x_1561_, 2);
lean_inc(v_scopes_1562_);
lean_dec(v___x_1561_);
v___x_1563_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1564_ = l_List_head_x21___redArg(v___x_1563_, v_scopes_1562_);
lean_dec(v_scopes_1562_);
v_opts_1565_ = lean_ctor_get(v___x_1564_, 1);
lean_inc_ref(v_opts_1565_);
lean_dec(v___x_1564_);
v_hasTrace_1566_ = lean_ctor_get_uint8(v_opts_1565_, sizeof(void*)*1);
if (v_hasTrace_1566_ == 0)
{
lean_dec_ref(v_opts_1565_);
lean_dec(v___x_1560_);
v___y_1497_ = v___x_1545_;
v___y_1498_ = v___x_1543_;
v___y_1499_ = v_snd_1533_;
v___y_1500_ = v___x_1552_;
v___y_1501_ = v_a_1558_;
v___y_1502_ = v___x_1538_;
v___y_1503_ = v_fst_1532_;
v___y_1504_ = v___x_1537_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1567_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1568_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__7, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7);
v___x_1569_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1560_, v_opts_1565_, v___x_1568_);
lean_dec_ref(v_opts_1565_);
lean_dec(v___x_1560_);
if (v___x_1569_ == 0)
{
v___y_1497_ = v___x_1545_;
v___y_1498_ = v___x_1543_;
v___y_1499_ = v_snd_1533_;
v___y_1500_ = v___x_1552_;
v___y_1501_ = v_a_1558_;
v___y_1502_ = v___x_1538_;
v___y_1503_ = v_fst_1532_;
v___y_1504_ = v___x_1537_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Elab_Command_getScope___redArg(v_a_1469_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v_currNamespace_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v_currNamespace_1572_ = lean_ctor_get(v_a_1571_, 2);
lean_inc(v_currNamespace_1572_);
lean_dec(v_a_1571_);
v___x_1573_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__9, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
lean_inc(v_a_1558_);
v___x_1574_ = l_Lean_Name_append(v_currNamespace_1572_, v_a_1558_);
v___x_1575_ = l_Lean_MessageData_ofName(v___x_1574_);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1573_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_1567_, v___x_1576_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_dec_ref_known(v___x_1577_, 1);
v___y_1497_ = v___x_1545_;
v___y_1498_ = v___x_1543_;
v___y_1499_ = v_snd_1533_;
v___y_1500_ = v___x_1552_;
v___y_1501_ = v_a_1558_;
v___y_1502_ = v___x_1538_;
v___y_1503_ = v_fst_1532_;
v___y_1504_ = v___x_1537_;
goto v___jp_1496_;
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_a_1558_);
lean_dec_ref(v___x_1552_);
lean_dec(v_snd_1533_);
lean_dec(v_fst_1532_);
lean_dec(v_stx_1467_);
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_a_1558_);
lean_dec_ref(v___x_1552_);
lean_dec(v_snd_1533_);
lean_dec(v_fst_1532_);
lean_dec(v_stx_1467_);
v_a_1586_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1570_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1570_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v___x_1552_);
lean_dec(v_snd_1533_);
lean_dec(v_fst_1532_);
lean_dec(v_stx_1467_);
v_a_1594_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1557_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1557_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_val_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v_scopes_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v_opts_1609_; uint8_t v_hasTrace_1610_; 
v_val_1602_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_val_1602_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1603_ = l_Lean_inheritedTraceOptions;
v___x_1604_ = lean_st_ref_get(v___x_1603_);
v___x_1605_ = lean_st_ref_get(v_a_1469_);
v_scopes_1606_ = lean_ctor_get(v___x_1605_, 2);
lean_inc(v_scopes_1606_);
lean_dec(v___x_1605_);
v___x_1607_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1608_ = l_List_head_x21___redArg(v___x_1607_, v_scopes_1606_);
lean_dec(v_scopes_1606_);
v_opts_1609_ = lean_ctor_get(v___x_1608_, 1);
lean_inc_ref(v_opts_1609_);
lean_dec(v___x_1608_);
v_hasTrace_1610_ = lean_ctor_get_uint8(v_opts_1609_, sizeof(void*)*1);
if (v_hasTrace_1610_ == 0)
{
lean_dec_ref(v_opts_1609_);
lean_dec(v___x_1604_);
v___y_1473_ = v___x_1545_;
v___y_1474_ = v___x_1543_;
v___y_1475_ = v___x_1552_;
v___y_1476_ = v_snd_1533_;
v___y_1477_ = v_fst_1532_;
v_declId_1478_ = v_val_1602_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1611_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1612_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__7, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7);
v___x_1613_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1604_, v_opts_1609_, v___x_1612_);
lean_dec_ref(v_opts_1609_);
lean_dec(v___x_1604_);
if (v___x_1613_ == 0)
{
v___y_1473_ = v___x_1545_;
v___y_1474_ = v___x_1543_;
v___y_1475_ = v___x_1552_;
v___y_1476_ = v_snd_1533_;
v___y_1477_ = v_fst_1532_;
v_declId_1478_ = v_val_1602_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = l_Lean_Syntax_getArgs(v_fst_1532_);
lean_inc(v_snd_1533_);
v___x_1615_ = l_Lean_Elab_Command_mkInstanceName(v___x_1614_, v_snd_1533_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_scopes_1619_; lean_object* v___x_1620_; lean_object* v_opts_1621_; uint8_t v_hasTrace_1622_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = lean_st_ref_get(v___x_1603_);
v___x_1618_ = lean_st_ref_get(v_a_1469_);
v_scopes_1619_ = lean_ctor_get(v___x_1618_, 2);
lean_inc(v_scopes_1619_);
lean_dec(v___x_1618_);
v___x_1620_ = l_List_head_x21___redArg(v___x_1607_, v_scopes_1619_);
lean_dec(v_scopes_1619_);
v_opts_1621_ = lean_ctor_get(v___x_1620_, 1);
lean_inc_ref(v_opts_1621_);
lean_dec(v___x_1620_);
v_hasTrace_1622_ = lean_ctor_get_uint8(v_opts_1621_, sizeof(void*)*1);
if (v_hasTrace_1622_ == 0)
{
lean_dec_ref(v_opts_1621_);
lean_dec(v___x_1617_);
lean_dec(v_a_1616_);
v___y_1473_ = v___x_1545_;
v___y_1474_ = v___x_1543_;
v___y_1475_ = v___x_1552_;
v___y_1476_ = v_snd_1533_;
v___y_1477_ = v_fst_1532_;
v_declId_1478_ = v_val_1602_;
goto v___jp_1472_;
}
else
{
uint8_t v___x_1623_; 
v___x_1623_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1617_, v_opts_1621_, v___x_1612_);
lean_dec_ref(v_opts_1621_);
lean_dec(v___x_1617_);
if (v___x_1623_ == 0)
{
lean_dec(v_a_1616_);
v___y_1473_ = v___x_1545_;
v___y_1474_ = v___x_1543_;
v___y_1475_ = v___x_1552_;
v___y_1476_ = v_snd_1533_;
v___y_1477_ = v_fst_1532_;
v_declId_1478_ = v_val_1602_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Elab_Command_getScope___redArg(v_a_1469_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v_currNamespace_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v_currNamespace_1626_ = lean_ctor_get(v_a_1625_, 2);
lean_inc(v_currNamespace_1626_);
lean_dec(v_a_1625_);
v___x_1627_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__9, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
v___x_1628_ = l_Lean_Name_append(v_currNamespace_1626_, v_a_1616_);
v___x_1629_ = l_Lean_MessageData_ofName(v___x_1628_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1627_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__11, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__11_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
lean_inc(v_val_1602_);
v___x_1633_ = l_Lean_MessageData_ofSyntax(v_val_1602_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_1611_, v___x_1634_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_dec_ref_known(v___x_1635_, 1);
v___y_1473_ = v___x_1545_;
v___y_1474_ = v___x_1543_;
v___y_1475_ = v___x_1552_;
v___y_1476_ = v_snd_1533_;
v___y_1477_ = v_fst_1532_;
v_declId_1478_ = v_val_1602_;
goto v___jp_1472_;
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_val_1602_);
lean_dec_ref(v___x_1552_);
lean_dec(v_snd_1533_);
lean_dec(v_fst_1532_);
lean_dec(v_stx_1467_);
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_a_1616_);
lean_dec(v_val_1602_);
lean_dec_ref(v___x_1552_);
lean_dec(v_snd_1533_);
lean_dec(v_fst_1532_);
lean_dec(v_stx_1467_);
v_a_1644_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1624_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1624_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_val_1602_);
lean_dec_ref(v___x_1552_);
lean_dec(v_snd_1533_);
lean_dec(v_fst_1532_);
lean_dec(v_stx_1467_);
v_a_1652_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1615_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1615_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
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
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v_a_1523_);
lean_dec(v_a_1521_);
lean_dec(v_a_1494_);
lean_dec(v_stx_1467_);
lean_dec_ref(v_modifiers_1466_);
v_a_1663_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1524_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1524_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_a_1521_);
lean_dec(v_a_1494_);
lean_dec(v_stx_1467_);
lean_dec_ref(v_modifiers_1466_);
v_a_1671_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1522_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1522_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec(v_a_1494_);
lean_dec(v_stx_1467_);
lean_dec_ref(v_modifiers_1466_);
v_a_1679_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1520_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1520_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
v___jp_1496_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1505_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0));
v___x_1506_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__1));
lean_inc_ref(v___y_1502_);
lean_inc_ref(v___y_1504_);
v___x_1507_ = l_Lean_Name_mkStr4(v___y_1504_, v___y_1502_, v___x_1505_, v___x_1506_);
v___x_1508_ = lean_unsigned_to_nat(1u);
v___x_1509_ = l_Lean_Syntax_getArg(v_stx_1467_, v___x_1508_);
v___x_1510_ = 1;
v___x_1511_ = l_Lean_mkIdentFrom(v___x_1509_, v___y_1501_, v___x_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = ((lean_object*)(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0));
lean_inc(v___y_1498_);
lean_inc_n(v___y_1497_, 2);
v___x_1513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1513_, 0, v___y_1497_);
lean_ctor_set(v___x_1513_, 1, v___y_1498_);
lean_ctor_set(v___x_1513_, 2, v___x_1512_);
v___x_1514_ = lean_mk_empty_array_with_capacity(v___x_1495_);
v___x_1515_ = lean_array_push(v___x_1514_, v___x_1511_);
v___x_1516_ = lean_array_push(v___x_1515_, v___x_1513_);
v___x_1517_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1517_, 0, v___y_1497_);
lean_ctor_set(v___x_1517_, 1, v___x_1507_);
lean_ctor_set(v___x_1517_, 2, v___x_1516_);
v___y_1473_ = v___y_1497_;
v___y_1474_ = v___y_1498_;
v___y_1475_ = v___y_1500_;
v___y_1476_ = v___y_1499_;
v___y_1477_ = v___y_1503_;
v_declId_1478_ = v___x_1517_;
goto v___jp_1472_;
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_stx_1467_);
lean_dec_ref(v_modifiers_1466_);
v_a_1687_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1493_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1493_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
v___jp_1472_:
{
lean_object* v_docString_x3f_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v_docString_x3f_1479_ = lean_ctor_get(v___y_1475_, 1);
lean_inc(v_docString_x3f_1479_);
v___x_1480_ = 1;
v___x_1481_ = l_Lean_Syntax_getArgs(v_stx_1467_);
v___x_1482_ = lean_unsigned_to_nat(5u);
v___x_1483_ = l_Array_toSubarray___redArg(v___x_1481_, v___x_1471_, v___x_1482_);
v___x_1484_ = l_Subarray_copy___redArg(v___x_1483_);
v___x_1485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___y_1473_);
lean_ctor_set(v___x_1485_, 1, v___y_1474_);
lean_ctor_set(v___x_1485_, 2, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___y_1476_);
v___x_1487_ = l_Lean_Syntax_getArg(v_stx_1467_, v___x_1482_);
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1489_, 0, v_stx_1467_);
lean_ctor_set(v___x_1489_, 1, v___x_1485_);
lean_ctor_set(v___x_1489_, 2, v___y_1475_);
lean_ctor_set(v___x_1489_, 3, v_declId_1478_);
lean_ctor_set(v___x_1489_, 4, v___y_1477_);
lean_ctor_set(v___x_1489_, 5, v___x_1486_);
lean_ctor_set(v___x_1489_, 6, v___x_1487_);
lean_ctor_set(v___x_1489_, 7, v_docString_x3f_1479_);
lean_ctor_set(v___x_1489_, 8, v___x_1488_);
lean_ctor_set(v___x_1489_, 9, v___x_1488_);
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*10, v___x_1480_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object* v_modifiers_1695_, lean_object* v_stx_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Elab_Command_mkDefViewOfInstance(v_modifiers_1695_, v_stx_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(lean_object* v_00_u03b1_1701_, lean_object* v_x_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_1702_, v___y_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1706_, lean_object* v_x_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(v_00_u03b1_1706_, v_x_1707_, v___y_1708_, v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec_ref(v_x_1707_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(lean_object* v_00_u03b1_1711_, lean_object* v_ref_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_1712_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1717_, lean_object* v_ref_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(v_00_u03b1_1717_, v_ref_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(lean_object* v_00_u03b1_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(v_00_u03b1_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(lean_object* v_00_u03b1_1733_, lean_object* v_x_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v_x_1734_, v___y_1735_, v___y_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___boxed(lean_object* v_00_u03b1_1739_, lean_object* v_x_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(v_00_u03b1_1739_, v_x_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(lean_object* v_msgData_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_1745_, v___y_1747_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___boxed(lean_object* v_msgData_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(v_msgData_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(lean_object* v_as_1755_, lean_object* v_as_x27_1756_, lean_object* v_b_1757_, lean_object* v_a_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_1756_, v_b_1757_, v___y_1759_, v___y_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___boxed(lean_object* v_as_1763_, lean_object* v_as_x27_1764_, lean_object* v_b_1765_, lean_object* v_a_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(v_as_1763_, v_as_x27_1764_, v_b_1765_, v_a_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v_as_x27_1764_);
lean_dec(v_as_1763_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(lean_object* v_00_u03b1_1771_, lean_object* v_ref_1772_, lean_object* v_msg_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_1772_, v_msg_1773_, v___y_1774_, v___y_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1778_, lean_object* v_ref_1779_, lean_object* v_msg_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(v_00_u03b1_1778_, v_ref_1779_, v_msg_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v_ref_1779_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1785_, lean_object* v_m_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_1786_, v_a_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_1789_, lean_object* v_m_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(v_00_u03b2_1789_, v_m_1790_, v_a_1791_);
lean_dec(v_a_1791_);
lean_dec_ref(v_m_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(lean_object* v_00_u03b1_1793_, lean_object* v_msg_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1794_, v___y_1795_, v___y_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1799_, lean_object* v_msg_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(v_00_u03b1_1799_, v_msg_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1804_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_){
_start:
{
uint8_t v___x_1808_; 
v___x_1808_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_1806_, v_x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
uint8_t v_res_1812_; lean_object* v_r_1813_; 
v_res_1812_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_1809_, v_x_1810_, v_x_1811_);
lean_dec_ref(v_x_1811_);
lean_dec_ref(v_x_1810_);
v_r_1813_ = lean_box(v_res_1812_);
return v_r_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1814_, lean_object* v_a_1815_, lean_object* v_x_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_1815_, v_x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1818_, lean_object* v_a_1819_, lean_object* v_x_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(v_00_u03b2_1818_, v_a_1819_, v_x_1820_);
lean_dec(v_x_1820_);
lean_dec(v_a_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(lean_object* v_msgData_1822_, lean_object* v_macroStack_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_1822_, v_macroStack_1823_, v___y_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___boxed(lean_object* v_msgData_1828_, lean_object* v_macroStack_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(v_msgData_1828_, v_macroStack_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
return v_res_1833_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_1834_, lean_object* v_x_1835_, size_t v_x_1836_, lean_object* v_x_1837_){
_start:
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_1835_, v_x_1836_, v_x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
size_t v_x_18705__boxed_1843_; uint8_t v_res_1844_; lean_object* v_r_1845_; 
v_x_18705__boxed_1843_ = lean_unbox_usize(v_x_1841_);
lean_dec(v_x_1841_);
v_res_1844_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_1839_, v_x_1840_, v_x_18705__boxed_1843_, v_x_1842_);
lean_dec_ref(v_x_1842_);
lean_dec_ref(v_x_1840_);
v_r_1845_ = lean_box(v_res_1844_);
return v_r_1845_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(lean_object* v_00_u03b2_1846_, lean_object* v_keys_1847_, lean_object* v_vals_1848_, lean_object* v_heq_1849_, lean_object* v_i_1850_, lean_object* v_k_1851_){
_start:
{
uint8_t v___x_1852_; 
v___x_1852_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_1847_, v_i_1850_, v_k_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___boxed(lean_object* v_00_u03b2_1853_, lean_object* v_keys_1854_, lean_object* v_vals_1855_, lean_object* v_heq_1856_, lean_object* v_i_1857_, lean_object* v_k_1858_){
_start:
{
uint8_t v_res_1859_; lean_object* v_r_1860_; 
v_res_1859_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(v_00_u03b2_1853_, v_keys_1854_, v_vals_1855_, v_heq_1856_, v_i_1857_, v_k_1858_);
lean_dec_ref(v_k_1858_);
lean_dec_ref(v_vals_1855_);
lean_dec_ref(v_keys_1854_);
v_r_1860_ = lean_box(v_res_1859_);
return v_r_1860_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6(void){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Array_mkArray0(lean_box(0));
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque(lean_object* v_modifiers_1885_, lean_object* v_stx_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_2024_; 
v___x_1890_ = lean_unsigned_to_nat(2u);
v___x_1891_ = l_Lean_Syntax_getArg(v_stx_1886_, v___x_1890_);
v___x_1892_ = l_Lean_Elab_expandDeclSig(v___x_1891_);
lean_dec(v___x_1891_);
v_fst_1893_ = lean_ctor_get(v___x_1892_, 0);
v_snd_1894_ = lean_ctor_get(v___x_1892_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_1896_ = v___x_1892_;
v_isShared_1897_ = v_isSharedCheck_2024_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_snd_1894_);
lean_inc(v_fst_1893_);
lean_dec(v___x_1892_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_2024_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_val_1899_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v_val_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = lean_unsigned_to_nat(3u);
v___x_1958_ = l_Lean_Syntax_getArg(v_stx_1886_, v___x_1957_);
v___x_1959_ = l_Lean_Syntax_getOptional_x3f(v___x_1958_);
lean_dec(v___x_1958_);
if (lean_obj_tag(v___x_1959_) == 0)
{
uint8_t v_isUnsafe_1960_; 
v_isUnsafe_1960_ = lean_ctor_get_uint8(v_modifiers_1885_, sizeof(void*)*3 + 4);
if (v_isUnsafe_1960_ == 0)
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_Elab_Command_getRef___redArg(v_a_1887_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1963_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref_known(v___x_1961_, 1);
v___x_1963_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1887_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_quotContext_x3f_1964_; lean_object* v___x_1965_; 
lean_dec_ref_known(v___x_1963_, 1);
v_quotContext_x3f_1964_ = lean_ctor_get(v_a_1887_, 5);
v___x_1965_ = l_Lean_SourceInfo_fromRef(v_a_1962_, v_isUnsafe_1960_);
lean_dec(v_a_1962_);
if (lean_obj_tag(v_quotContext_x3f_1964_) == 0)
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1888_);
lean_dec_ref(v___x_1974_);
goto v___jp_1966_;
}
else
{
goto v___jp_1966_;
}
v___jp_1966_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1967_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9));
v___x_1968_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10));
lean_inc_n(v___x_1965_, 2);
v___x_1969_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1965_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1971_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6, &l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once, _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6);
v___x_1972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1965_);
lean_ctor_set(v___x_1972_, 1, v___x_1970_);
lean_ctor_set(v___x_1972_, 2, v___x_1971_);
v___x_1973_ = l_Lean_Syntax_node2(v___x_1965_, v___x_1967_, v___x_1969_, v___x_1972_);
v_val_1931_ = v___x_1973_;
v___y_1932_ = v_a_1887_;
v___y_1933_ = v_a_1888_;
goto v___jp_1930_;
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec(v_a_1962_);
lean_del_object(v___x_1896_);
lean_dec(v_snd_1894_);
lean_dec(v_fst_1893_);
lean_dec(v_stx_1886_);
lean_dec_ref(v_modifiers_1885_);
v_a_1975_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1963_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1963_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_del_object(v___x_1896_);
lean_dec(v_snd_1894_);
lean_dec(v_fst_1893_);
lean_dec(v_stx_1886_);
lean_dec_ref(v_modifiers_1885_);
v_a_1983_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1961_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1961_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Elab_Command_getRef___redArg(v_a_1887_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___x_1993_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1887_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_quotContext_x3f_1994_; uint8_t v___x_1995_; lean_object* v___x_1996_; 
lean_dec_ref_known(v___x_1993_, 1);
v_quotContext_x3f_1994_ = lean_ctor_get(v_a_1887_, 5);
v___x_1995_ = 0;
v___x_1996_ = l_Lean_SourceInfo_fromRef(v_a_1992_, v___x_1995_);
lean_dec(v_a_1992_);
if (lean_obj_tag(v_quotContext_x3f_1994_) == 0)
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1888_);
lean_dec_ref(v___x_2006_);
goto v___jp_1997_;
}
else
{
goto v___jp_1997_;
}
v___jp_1997_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_1998_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9));
v___x_1999_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10));
lean_inc_n(v___x_1996_, 3);
v___x_2000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1996_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_2002_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11));
v___x_2003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_1996_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = l_Lean_Syntax_node1(v___x_1996_, v___x_2001_, v___x_2003_);
v___x_2005_ = l_Lean_Syntax_node2(v___x_1996_, v___x_1998_, v___x_2000_, v___x_2004_);
v_val_1931_ = v___x_2005_;
v___y_1932_ = v_a_1887_;
v___y_1933_ = v_a_1888_;
goto v___jp_1930_;
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v_a_1992_);
lean_del_object(v___x_1896_);
lean_dec(v_snd_1894_);
lean_dec(v_fst_1893_);
lean_dec(v_stx_1886_);
lean_dec_ref(v_modifiers_1885_);
v_a_2007_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1993_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1993_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_del_object(v___x_1896_);
lean_dec(v_snd_1894_);
lean_dec(v_fst_1893_);
lean_dec(v_stx_1886_);
lean_dec_ref(v_modifiers_1885_);
v_a_2015_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1991_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1991_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
else
{
lean_object* v_val_2023_; 
lean_del_object(v___x_1896_);
v_val_2023_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_val_2023_);
lean_dec_ref_known(v___x_1959_, 1);
v_val_1899_ = v_val_2023_;
goto v___jp_1898_;
}
v___jp_1898_:
{
lean_object* v_docString_x3f_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_docString_x3f_1900_ = lean_ctor_get(v_modifiers_1885_, 1);
lean_inc(v_docString_x3f_1900_);
v___x_1901_ = 4;
v___x_1902_ = l_Lean_Syntax_getArgs(v_stx_1886_);
v___x_1903_ = lean_unsigned_to_nat(3u);
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = l_Array_toSubarray___redArg(v___x_1902_, v___x_1904_, v___x_1903_);
v___x_1906_ = l_Subarray_copy___redArg(v___x_1905_);
v___x_1907_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1908_ = lean_box(2);
v___x_1909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
lean_ctor_set(v___x_1909_, 1, v___x_1907_);
lean_ctor_set(v___x_1909_, 2, v___x_1906_);
v___x_1910_ = lean_unsigned_to_nat(1u);
v___x_1911_ = l_Lean_Syntax_getArg(v_stx_1886_, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_snd_1894_);
v___x_1913_ = lean_box(0);
v___x_1914_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1914_, 0, v_stx_1886_);
lean_ctor_set(v___x_1914_, 1, v___x_1909_);
lean_ctor_set(v___x_1914_, 2, v_modifiers_1885_);
lean_ctor_set(v___x_1914_, 3, v___x_1911_);
lean_ctor_set(v___x_1914_, 4, v_fst_1893_);
lean_ctor_set(v___x_1914_, 5, v___x_1912_);
lean_ctor_set(v___x_1914_, 6, v_val_1899_);
lean_ctor_set(v___x_1914_, 7, v_docString_x3f_1900_);
lean_ctor_set(v___x_1914_, 8, v___x_1913_);
lean_ctor_set(v___x_1914_, 9, v___x_1913_);
lean_ctor_set_uint8(v___x_1914_, sizeof(void*)*10, v___x_1901_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
v___jp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1919_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1));
v___x_1920_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2));
lean_inc(v___y_1917_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 2);
lean_ctor_set(v___x_1896_, 1, v___x_1920_);
lean_ctor_set(v___x_1896_, 0, v___y_1917_);
v___x_1922_ = v___x_1896_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___y_1917_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1923_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5));
v___x_1924_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1925_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6, &l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once, _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6);
lean_inc_n(v___y_1917_, 2);
v___x_1926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1926_, 0, v___y_1917_);
lean_ctor_set(v___x_1926_, 1, v___x_1924_);
lean_ctor_set(v___x_1926_, 2, v___x_1925_);
lean_inc_ref_n(v___x_1926_, 2);
v___x_1927_ = l_Lean_Syntax_node2(v___y_1917_, v___x_1923_, v___x_1926_, v___x_1926_);
v___x_1928_ = l_Lean_Syntax_node4(v___y_1917_, v___x_1919_, v___x_1922_, v___y_1918_, v___x_1927_, v___x_1926_);
v_val_1899_ = v___x_1928_;
goto v___jp_1898_;
}
}
v___jp_1930_:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_Elab_Command_getRef___redArg(v___y_1932_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1936_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1932_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_quotContext_x3f_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; 
lean_dec_ref_known(v___x_1936_, 1);
v_quotContext_x3f_1937_ = lean_ctor_get(v___y_1932_, 5);
v___x_1938_ = 0;
v___x_1939_ = l_Lean_SourceInfo_fromRef(v_a_1935_, v___x_1938_);
lean_dec(v_a_1935_);
if (lean_obj_tag(v_quotContext_x3f_1937_) == 0)
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_1933_);
lean_dec_ref(v___x_1940_);
v___y_1917_ = v___x_1939_;
v___y_1918_ = v_val_1931_;
goto v___jp_1916_;
}
else
{
v___y_1917_ = v___x_1939_;
v___y_1918_ = v_val_1931_;
goto v___jp_1916_;
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v_a_1935_);
lean_dec(v_val_1931_);
lean_del_object(v___x_1896_);
lean_dec(v_snd_1894_);
lean_dec(v_fst_1893_);
lean_dec(v_stx_1886_);
lean_dec_ref(v_modifiers_1885_);
v_a_1941_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1936_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1936_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_val_1931_);
lean_del_object(v___x_1896_);
lean_dec(v_snd_1894_);
lean_dec(v_fst_1893_);
lean_dec(v_stx_1886_);
lean_dec_ref(v_modifiers_1885_);
v_a_1949_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1934_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1934_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___boxed(lean_object* v_modifiers_2025_, lean_object* v_stx_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_Elab_Command_mkDefViewOfOpaque(v_modifiers_2025_, v_stx_2026_, v_a_2027_, v_a_2028_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object* v_modifiers_2043_, lean_object* v_stx_2044_){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v_fst_2048_; lean_object* v_snd_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_docString_x3f_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; lean_object* v_id_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = l_Lean_Syntax_getArg(v_stx_2044_, v___x_2045_);
v___x_2047_ = l_Lean_Elab_expandOptDeclSig(v___x_2046_);
lean_dec(v___x_2046_);
v_fst_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_fst_2048_);
v_snd_2049_ = lean_ctor_get(v___x_2047_, 1);
lean_inc(v_snd_2049_);
lean_dec_ref(v___x_2047_);
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_2052_ = lean_box(2);
v___x_2053_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__0));
v_docString_x3f_2054_ = lean_ctor_get(v_modifiers_2043_, 1);
lean_inc(v_docString_x3f_2054_);
v___x_2055_ = l_Lean_Syntax_getArg(v_stx_2044_, v___x_2050_);
v___x_2056_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__2));
v___x_2057_ = 1;
v_id_2058_ = l_Lean_mkIdentFrom(v___x_2055_, v___x_2056_, v___x_2057_);
lean_dec(v___x_2055_);
v___x_2059_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__3));
v___x_2060_ = lean_unsigned_to_nat(2u);
v___x_2061_ = lean_mk_empty_array_with_capacity(v___x_2060_);
v___x_2062_ = lean_array_push(v___x_2061_, v_id_2058_);
v___x_2063_ = lean_array_push(v___x_2062_, v___x_2053_);
v___x_2064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2052_);
lean_ctor_set(v___x_2064_, 1, v___x_2059_);
lean_ctor_set(v___x_2064_, 2, v___x_2063_);
v___x_2065_ = 3;
v___x_2066_ = l_Lean_Syntax_getArgs(v_stx_2044_);
v___x_2067_ = l_Array_toSubarray___redArg(v___x_2066_, v___x_2050_, v___x_2060_);
v___x_2068_ = l_Subarray_copy___redArg(v___x_2067_);
v___x_2069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2052_);
lean_ctor_set(v___x_2069_, 1, v___x_2051_);
lean_ctor_set(v___x_2069_, 2, v___x_2068_);
v___x_2070_ = l_Lean_Syntax_getArg(v_stx_2044_, v___x_2060_);
v___x_2071_ = lean_box(0);
v___x_2072_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2072_, 0, v_stx_2044_);
lean_ctor_set(v___x_2072_, 1, v___x_2069_);
lean_ctor_set(v___x_2072_, 2, v_modifiers_2043_);
lean_ctor_set(v___x_2072_, 3, v___x_2064_);
lean_ctor_set(v___x_2072_, 4, v_fst_2048_);
lean_ctor_set(v___x_2072_, 5, v_snd_2049_);
lean_ctor_set(v___x_2072_, 6, v___x_2070_);
lean_ctor_set(v___x_2072_, 7, v_docString_x3f_2054_);
lean_ctor_set(v___x_2072_, 8, v___x_2071_);
lean_ctor_set(v___x_2072_, 9, v___x_2071_);
lean_ctor_set_uint8(v___x_2072_, sizeof(void*)*10, v___x_2065_);
return v___x_2072_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_isDefLike(lean_object* v_stx_2108_){
_start:
{
lean_object* v_declKind_2109_; uint8_t v___y_2111_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v_declKind_2109_ = l_Lean_Syntax_getKind(v_stx_2108_);
v___x_2120_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__8));
v___x_2121_ = lean_name_eq(v_declKind_2109_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__10));
v___x_2123_ = lean_name_eq(v_declKind_2109_, v___x_2122_);
v___y_2111_ = v___x_2123_;
goto v___jp_2110_;
}
else
{
v___y_2111_ = v___x_2121_;
goto v___jp_2110_;
}
v___jp_2110_:
{
if (v___y_2111_ == 0)
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2113_ = lean_name_eq(v_declKind_2109_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__3));
v___x_2115_ = lean_name_eq(v_declKind_2109_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__4));
v___x_2117_ = lean_name_eq(v_declKind_2109_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2119_ = lean_name_eq(v_declKind_2109_, v___x_2118_);
lean_dec(v_declKind_2109_);
return v___x_2119_;
}
else
{
lean_dec(v_declKind_2109_);
return v___x_2117_;
}
}
else
{
lean_dec(v_declKind_2109_);
return v___x_2115_;
}
}
else
{
lean_dec(v_declKind_2109_);
return v___x_2113_;
}
}
else
{
lean_dec(v_declKind_2109_);
return v___y_2111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object* v_stx_2124_){
_start:
{
uint8_t v_res_2125_; lean_object* v_r_2126_; 
v_res_2125_ = l_Lean_Elab_Command_isDefLike(v_stx_2124_);
v_r_2126_ = lean_box(v_res_2125_);
return v_r_2126_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefView___closed__1(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = ((lean_object*)(l_Lean_Elab_Command_mkDefView___closed__0));
v___x_2129_ = l_Lean_stringToMessageData(v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView(lean_object* v_modifiers_2130_, lean_object* v_stx_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_Elab_Command_getScope___redArg(v_a_2133_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2205_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2205_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2205_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_stx_2140_; lean_object* v_docString_x3f_2141_; uint8_t v_visibility_2142_; uint8_t v_isProtected_2143_; uint8_t v_computeKind_2144_; uint8_t v_recKind_2145_; uint8_t v_isUnsafe_2146_; lean_object* v_attrs_2147_; lean_object* v_declKind_2148_; lean_object* v___y_2150_; uint8_t v___y_2184_; uint8_t v___x_2202_; uint8_t v___x_2203_; 
v_stx_2140_ = lean_ctor_get(v_modifiers_2130_, 0);
v_docString_x3f_2141_ = lean_ctor_get(v_modifiers_2130_, 1);
v_visibility_2142_ = lean_ctor_get_uint8(v_modifiers_2130_, sizeof(void*)*3);
v_isProtected_2143_ = lean_ctor_get_uint8(v_modifiers_2130_, sizeof(void*)*3 + 1);
v_computeKind_2144_ = lean_ctor_get_uint8(v_modifiers_2130_, sizeof(void*)*3 + 2);
v_recKind_2145_ = lean_ctor_get_uint8(v_modifiers_2130_, sizeof(void*)*3 + 3);
v_isUnsafe_2146_ = lean_ctor_get_uint8(v_modifiers_2130_, sizeof(void*)*3 + 4);
v_attrs_2147_ = lean_ctor_get(v_modifiers_2130_, 2);
lean_inc(v_stx_2131_);
v_declKind_2148_ = l_Lean_Syntax_getKind(v_stx_2131_);
v___x_2202_ = 0;
v___x_2203_ = l_Lean_Elab_instBEqComputeKind_beq(v_computeKind_2144_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_dec(v_a_2136_);
v___y_2184_ = v___x_2203_;
goto v___jp_2183_;
}
else
{
uint8_t v_isMeta_2204_; 
v_isMeta_2204_ = lean_ctor_get_uint8(v_a_2136_, sizeof(void*)*10 + 2);
lean_dec(v_a_2136_);
v___y_2184_ = v_isMeta_2204_;
goto v___jp_2183_;
}
v___jp_2149_:
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__8));
v___x_2152_ = lean_name_eq(v_declKind_2148_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__10));
v___x_2154_ = lean_name_eq(v_declKind_2148_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2156_ = lean_name_eq(v_declKind_2148_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__3));
v___x_2158_ = lean_name_eq(v_declKind_2148_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2159_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__4));
v___x_2160_ = lean_name_eq(v_declKind_2148_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2162_ = lean_name_eq(v_declKind_2148_, v___x_2161_);
lean_dec(v_declKind_2148_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec_ref(v___y_2150_);
lean_del_object(v___x_2138_);
lean_dec(v_stx_2131_);
v___x_2163_ = lean_obj_once(&l_Lean_Elab_Command_mkDefView___closed__1, &l_Lean_Elab_Command_mkDefView___closed__1_once, _init_l_Lean_Elab_Command_mkDefView___closed__1);
v___x_2164_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v___x_2163_, v_a_2132_, v_a_2133_);
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = l_Lean_Elab_Command_mkDefViewOfExample(v___y_2150_, v_stx_2131_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2165_);
v___x_2167_ = v___x_2138_;
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
else
{
lean_object* v___x_2169_; 
lean_dec(v_declKind_2148_);
lean_del_object(v___x_2138_);
v___x_2169_ = l_Lean_Elab_Command_mkDefViewOfInstance(v___y_2150_, v_stx_2131_, v_a_2132_, v_a_2133_);
return v___x_2169_;
}
}
else
{
lean_object* v___x_2170_; 
lean_dec(v_declKind_2148_);
lean_del_object(v___x_2138_);
v___x_2170_ = l_Lean_Elab_Command_mkDefViewOfOpaque(v___y_2150_, v_stx_2131_, v_a_2132_, v_a_2133_);
return v___x_2170_;
}
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
lean_dec(v_declKind_2148_);
v___x_2171_ = l_Lean_Elab_Command_mkDefViewOfTheorem(v___y_2150_, v_stx_2131_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2171_);
v___x_2173_ = v___x_2138_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
lean_dec(v_declKind_2148_);
v___x_2175_ = l_Lean_Elab_Command_mkDefViewOfDef(v___y_2150_, v_stx_2131_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2175_);
v___x_2177_ = v___x_2138_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
lean_dec(v_declKind_2148_);
v___x_2179_ = l_Lean_Elab_Command_mkDefViewOfAbbrev(v___y_2150_, v_stx_2131_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2179_);
v___x_2181_ = v___x_2138_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
v___jp_2183_:
{
if (v___y_2184_ == 0)
{
v___y_2150_ = v_modifiers_2130_;
goto v___jp_2149_;
}
else
{
lean_object* v___x_2185_; uint8_t v___x_2186_; uint8_t v___x_2187_; 
v___x_2185_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2186_ = lean_name_eq(v_declKind_2148_, v___x_2185_);
v___x_2187_ = lean_bool_not(v___x_2186_);
if (v___x_2187_ == 0)
{
v___y_2150_ = v_modifiers_2130_;
goto v___jp_2149_;
}
else
{
lean_object* v___x_2188_; uint8_t v___x_2189_; uint8_t v___x_2190_; 
v___x_2188_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2189_ = lean_name_eq(v_declKind_2148_, v___x_2188_);
v___x_2190_ = lean_bool_not(v___x_2189_);
if (v___x_2190_ == 0)
{
v___y_2150_ = v_modifiers_2130_;
goto v___jp_2149_;
}
else
{
lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2198_; 
lean_inc_ref(v_attrs_2147_);
lean_inc(v_docString_x3f_2141_);
lean_inc(v_stx_2140_);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_modifiers_2130_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; lean_object* v_unused_2200_; lean_object* v_unused_2201_; 
v_unused_2199_ = lean_ctor_get(v_modifiers_2130_, 2);
lean_dec(v_unused_2199_);
v_unused_2200_ = lean_ctor_get(v_modifiers_2130_, 1);
lean_dec(v_unused_2200_);
v_unused_2201_ = lean_ctor_get(v_modifiers_2130_, 0);
lean_dec(v_unused_2201_);
v___x_2192_ = v_modifiers_2130_;
v_isShared_2193_ = v_isSharedCheck_2198_;
goto v_resetjp_2191_;
}
else
{
lean_dec(v_modifiers_2130_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2198_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
uint8_t v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = 1;
if (v_isShared_2193_ == 0)
{
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_stx_2140_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_docString_x3f_2141_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_attrs_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2197_, sizeof(void*)*3, v_visibility_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2197_, sizeof(void*)*3 + 1, v_isProtected_2143_);
lean_ctor_set_uint8(v_reuseFailAlloc_2197_, sizeof(void*)*3 + 3, v_recKind_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2197_, sizeof(void*)*3 + 4, v_isUnsafe_2146_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_ctor_set_uint8(v___x_2196_, sizeof(void*)*3 + 2, v___x_2194_);
v___y_2150_ = v___x_2196_;
goto v___jp_2149_;
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
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_stx_2131_);
lean_dec_ref(v_modifiers_2130_);
v_a_2206_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2135_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2135_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object* v_modifiers_2214_, lean_object* v_stx_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_Elab_Command_mkDefView(v_modifiers_2214_, v_stx_2215_, v_a_2216_, v_a_2217_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2281_; uint8_t v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2281_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2282_ = 0;
v___x_2283_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2284_ = l_Lean_registerTraceClass(v___x_2281_, v___x_2282_, v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2____boxed(lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_();
return v_res_2286_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_unsigned_to_nat(2390142386u);
v___x_2288_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2289_ = l_Lean_Name_num___override(v___x_2288_, v___x_2287_);
return v___x_2289_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2291_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2292_ = l_Lean_Name_str___override(v___x_2291_, v___x_2290_);
return v___x_2292_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2294_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2295_ = l_Lean_Name_str___override(v___x_2294_, v___x_2293_);
return v___x_2295_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_unsigned_to_nat(2u);
v___x_2297_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2298_ = l_Lean_Name_num___override(v___x_2297_, v___x_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2300_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_2301_ = 0;
v___x_2302_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2303_ = l_Lean_registerTraceClass(v___x_2300_, v___x_2301_, v___x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2____boxed(lean_object* v_a_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_();
return v_res_2305_;
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
