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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Elab_DefKind_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_DefKind_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Elab_DefKind_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___redArg(lean_object* v_def_22_){
_start:
{
lean_inc(v_def_22_);
return v_def_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___redArg___boxed(lean_object* v_def_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Elab_DefKind_def_elim___redArg(v_def_23_);
lean_dec(v_def_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_def_28_){
_start:
{
lean_inc(v_def_28_);
return v_def_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_def_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_def_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Elab_DefKind_def_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_def_32_);
lean_dec(v_def_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___redArg(lean_object* v_instance_35_){
_start:
{
lean_inc(v_instance_35_);
return v_instance_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___redArg___boxed(lean_object* v_instance_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Elab_DefKind_instance_elim___redArg(v_instance_36_);
lean_dec(v_instance_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_instance_41_){
_start:
{
lean_inc(v_instance_41_);
return v_instance_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_instance_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_instance_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Elab_DefKind_instance_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_instance_45_);
lean_dec(v_instance_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___redArg(lean_object* v_theorem_48_){
_start:
{
lean_inc(v_theorem_48_);
return v_theorem_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___redArg___boxed(lean_object* v_theorem_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Elab_DefKind_theorem_elim___redArg(v_theorem_49_);
lean_dec(v_theorem_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_theorem_54_){
_start:
{
lean_inc(v_theorem_54_);
return v_theorem_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_theorem_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_theorem_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Elab_DefKind_theorem_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_theorem_58_);
lean_dec(v_theorem_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___redArg(lean_object* v_example_61_){
_start:
{
lean_inc(v_example_61_);
return v_example_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___redArg___boxed(lean_object* v_example_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Elab_DefKind_example_elim___redArg(v_example_62_);
lean_dec(v_example_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_example_67_){
_start:
{
lean_inc(v_example_67_);
return v_example_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_example_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_example_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Lean_Elab_DefKind_example_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_example_71_);
lean_dec(v_example_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___redArg(lean_object* v_opaque_74_){
_start:
{
lean_inc(v_opaque_74_);
return v_opaque_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___redArg___boxed(lean_object* v_opaque_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Elab_DefKind_opaque_elim___redArg(v_opaque_75_);
lean_dec(v_opaque_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_opaque_80_){
_start:
{
lean_inc(v_opaque_80_);
return v_opaque_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_opaque_elim___boxed(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_opaque_84_){
_start:
{
uint8_t v_t_boxed_85_; lean_object* v_res_86_; 
v_t_boxed_85_ = lean_unbox(v_t_82_);
v_res_86_ = l_Lean_Elab_DefKind_opaque_elim(v_motive_81_, v_t_boxed_85_, v_h_83_, v_opaque_84_);
lean_dec(v_opaque_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___redArg(lean_object* v_abbrev_87_){
_start:
{
lean_inc(v_abbrev_87_);
return v_abbrev_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___redArg___boxed(lean_object* v_abbrev_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Elab_DefKind_abbrev_elim___redArg(v_abbrev_88_);
lean_dec(v_abbrev_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim(lean_object* v_motive_90_, uint8_t v_t_91_, lean_object* v_h_92_, lean_object* v_abbrev_93_){
_start:
{
lean_inc(v_abbrev_93_);
return v_abbrev_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_abbrev_elim___boxed(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_abbrev_97_){
_start:
{
uint8_t v_t_boxed_98_; lean_object* v_res_99_; 
v_t_boxed_98_ = lean_unbox(v_t_95_);
v_res_99_ = l_Lean_Elab_DefKind_abbrev_elim(v_motive_94_, v_t_boxed_98_, v_h_96_, v_abbrev_97_);
lean_dec(v_abbrev_97_);
return v_res_99_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedDefKind_default(void){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedDefKind(void){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqDefKind_beq(uint8_t v_x_102_, uint8_t v_y_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_104_ = lean_box(v_x_102_);
v___x_105_ = lean_obj_tag_nat(v___x_104_);
lean_dec(v___x_104_);
v___x_106_ = lean_box(v_y_103_);
v___x_107_ = lean_obj_tag_nat(v___x_106_);
lean_dec(v___x_106_);
v___x_108_ = lean_nat_dec_eq(v___x_105_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqDefKind_beq___boxed(lean_object* v_x_109_, lean_object* v_y_110_){
_start:
{
uint8_t v_x_24__boxed_111_; uint8_t v_y_25__boxed_112_; uint8_t v_res_113_; lean_object* v_r_114_; 
v_x_24__boxed_111_ = lean_unbox(v_x_109_);
v_y_25__boxed_112_ = lean_unbox(v_y_110_);
v_res_113_ = l_Lean_Elab_instBEqDefKind_beq(v_x_24__boxed_111_, v_y_25__boxed_112_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t v_x_117_){
_start:
{
if (v_x_117_ == 2)
{
uint8_t v___x_118_; 
v___x_118_ = 1;
return v___x_118_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = 0;
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isTheorem___boxed(lean_object* v_x_120_){
_start:
{
uint8_t v_x_17__boxed_121_; uint8_t v_res_122_; lean_object* v_r_123_; 
v_x_17__boxed_121_ = lean_unbox(v_x_120_);
v_res_122_ = l_Lean_Elab_DefKind_isTheorem(v_x_17__boxed_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isExample(uint8_t v_x_124_){
_start:
{
if (v_x_124_ == 3)
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
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isExample___boxed(lean_object* v_x_127_){
_start:
{
uint8_t v_x_17__boxed_128_; uint8_t v_res_129_; lean_object* v_r_130_; 
v_x_17__boxed_128_ = lean_unbox(v_x_127_);
v_res_129_ = l_Lean_Elab_DefKind_isExample(v_x_17__boxed_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_box(0);
v___x_137_ = ((lean_object*)(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2));
v___x_138_ = l_Lean_Expr_const___override(v___x_137_, v___x_136_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_139_ = lean_obj_once(&l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3, &l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3_once, _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = ((lean_object*)(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0));
v___x_142_ = lean_box(0);
v___x_143_ = lean_box(0);
v___x_144_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
lean_ctor_set(v___x_144_, 2, v___x_142_);
lean_ctor_set(v___x_144_, 3, v___x_141_);
lean_ctor_set(v___x_144_, 4, v___x_140_);
lean_ctor_set(v___x_144_, 5, v___x_139_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default(void){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4, &l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4_once, _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData(void){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Elab_instInhabitedDefViewElabHeaderData_default;
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(lean_object* v___f_147_, lean_object* v_x_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_x_148_, v___f_147_, v___y_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed(lean_object* v___f_151_, lean_object* v_x_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(v___f_151_, v_x_152_, v___y_153_);
lean_dec_ref(v___y_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1(lean_object* v___x_155_, lean_object* v___f_156_, lean_object* v_s_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_toSnapshot_159_; lean_object* v_moreSnaps_160_; lean_object* v___x_161_; size_t v_sz_162_; size_t v___x_163_; lean_object* v___x_249__overap_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_toSnapshot_159_ = lean_ctor_get(v_s_157_, 0);
lean_inc_ref(v_toSnapshot_159_);
v_moreSnaps_160_ = lean_ctor_get(v_s_157_, 3);
lean_inc_ref(v_moreSnaps_160_);
lean_dec_ref(v_s_157_);
v___x_161_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_159_, v___y_158_);
v_sz_162_ = lean_array_size(v_moreSnaps_160_);
v___x_163_ = ((size_t)0ULL);
v___x_249__overap_164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_155_, v___f_156_, v_sz_162_, v___x_163_, v_moreSnaps_160_);
lean_inc_ref(v___y_158_);
v___x_165_ = lean_apply_1(v___x_249__overap_164_, v___y_158_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_161_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1___boxed(lean_object* v___x_167_, lean_object* v___f_168_, lean_object* v_s_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1(v___x_167_, v___f_168_, v_s_169_, v___y_170_);
lean_dec_ref(v___y_170_);
return v_res_171_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__9));
v___x_192_ = l_ReaderT_instMonad___redArg(v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13(void){
_start:
{
lean_object* v___f_196_; lean_object* v___x_197_; lean_object* v___f_198_; 
v___f_196_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__12));
v___x_197_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10);
v___f_198_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__1___boxed), 4, 2);
lean_closure_set(v___f_198_, 0, v___x_197_);
lean_closure_set(v___f_198_, 1, v___f_196_);
return v___f_198_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot(void){
_start:
{
lean_object* v___f_199_; 
v___f_199_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__13);
return v___f_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(lean_object* v___x_200_, lean_object* v_x_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_x_201_, v___x_200_, v___y_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(lean_object* v___x_204_, lean_object* v_x_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(v___x_204_, v_x_205_, v___y_206_);
lean_dec_ref(v___y_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2(lean_object* v___x_210_, lean_object* v___f_211_, lean_object* v___f_212_, lean_object* v___f_213_, lean_object* v_s_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_toSnapshot_216_; lean_object* v_tacSnap_x3f_217_; lean_object* v_bodySnap_218_; lean_object* v_moreSnaps_219_; lean_object* v___x_220_; lean_object* v___y_222_; 
v_toSnapshot_216_ = lean_ctor_get(v_s_214_, 0);
lean_inc_ref(v_toSnapshot_216_);
v_tacSnap_x3f_217_ = lean_ctor_get(v_s_214_, 4);
lean_inc(v_tacSnap_x3f_217_);
v_bodySnap_218_ = lean_ctor_get(v_s_214_, 6);
lean_inc_ref(v_bodySnap_218_);
v_moreSnaps_219_ = lean_ctor_get(v_s_214_, 7);
lean_inc_ref(v_moreSnaps_219_);
lean_dec_ref(v_s_214_);
v___x_220_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_216_, v___y_215_);
if (lean_obj_tag(v_tacSnap_x3f_217_) == 0)
{
lean_object* v___x_237_; 
v___x_237_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___closed__0));
v___y_222_ = v___x_237_;
goto v___jp_221_;
}
else
{
lean_object* v_val_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_val_238_ = lean_ctor_get(v_tacSnap_x3f_217_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v_tacSnap_x3f_217_, 1);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_mk_empty_array_with_capacity(v___x_239_);
v___x_241_ = lean_array_push(v___x_240_, v_val_238_);
v___y_222_ = v___x_241_;
goto v___jp_221_;
}
v___jp_221_:
{
size_t v_sz_223_; size_t v___x_224_; lean_object* v___x_513__overap_225_; lean_object* v___x_226_; lean_object* v___x_227_; size_t v_sz_228_; lean_object* v___x_515__overap_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_sz_223_ = lean_array_size(v___y_222_);
v___x_224_ = ((size_t)0ULL);
lean_inc_ref(v___x_210_);
v___x_513__overap_225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_210_, v___f_211_, v_sz_223_, v___x_224_, v___y_222_);
lean_inc_ref_n(v___y_215_, 2);
v___x_226_ = lean_apply_1(v___x_513__overap_225_, v___y_215_);
v___x_227_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_bodySnap_218_, v___f_212_, v___y_215_);
v_sz_228_ = lean_array_size(v_moreSnaps_219_);
v___x_515__overap_229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_210_, v___f_213_, v_sz_228_, v___x_224_, v_moreSnaps_219_);
v___x_230_ = lean_apply_1(v___x_515__overap_229_, v___y_215_);
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_mk_empty_array_with_capacity(v___x_231_);
v___x_233_ = lean_array_push(v___x_232_, v___x_227_);
v___x_234_ = l_Array_append___redArg(v___x_226_, v___x_233_);
lean_dec_ref(v___x_233_);
v___x_235_ = l_Array_append___redArg(v___x_234_, v___x_230_);
lean_dec_ref(v___x_230_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_220_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___boxed(lean_object* v___x_242_, lean_object* v___f_243_, lean_object* v___f_244_, lean_object* v___f_245_, lean_object* v_s_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2(v___x_242_, v___f_243_, v___f_244_, v___f_245_, v_s_246_, v___y_247_);
lean_dec_ref(v___y_247_);
return v_res_248_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2(void){
_start:
{
lean_object* v___x_252_; lean_object* v___f_253_; 
v___x_252_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot;
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_253_, 0, v___x_252_);
return v___f_253_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3(void){
_start:
{
lean_object* v___f_254_; lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___f_258_; 
v___f_254_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__12));
v___f_255_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2, &l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2_once, _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__2);
v___f_256_ = ((lean_object*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1));
v___x_257_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10);
v___f_258_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__2___boxed), 6, 4);
lean_closure_set(v___f_258_, 0, v___x_257_);
lean_closure_set(v___f_258_, 1, v___f_256_);
lean_closure_set(v___f_258_, 2, v___f_255_);
lean_closure_set(v___f_258_, 3, v___f_254_);
return v___f_258_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot(void){
_start:
{
lean_object* v___f_259_; 
v___f_259_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3, &l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3_once, _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__3);
return v___f_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(lean_object* v___f_269_, lean_object* v_x_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_headerProcessedSnap_272_; lean_object* v___x_273_; 
v_headerProcessedSnap_272_ = lean_ctor_get(v_x_270_, 1);
lean_inc_ref(v_headerProcessedSnap_272_);
lean_dec_ref(v_x_270_);
v___x_273_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_headerProcessedSnap_272_, v___f_269_, v___y_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0___boxed(lean_object* v___f_274_, lean_object* v_x_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(v___f_274_, v_x_275_, v___y_276_);
lean_dec_ref(v___y_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(lean_object* v___x_278_, lean_object* v___f_279_, lean_object* v_s_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_toSnapshot_282_; lean_object* v_defs_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_295_; 
v_toSnapshot_282_ = lean_ctor_get(v_s_280_, 0);
v_defs_283_ = lean_ctor_get(v_s_280_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v_s_280_);
if (v_isSharedCheck_295_ == 0)
{
v___x_285_ = v_s_280_;
v_isShared_286_ = v_isSharedCheck_295_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_defs_283_);
lean_inc(v_toSnapshot_282_);
lean_dec(v_s_280_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_295_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; size_t v_sz_288_; size_t v___x_289_; lean_object* v___x_253__overap_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_287_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_282_, v___y_281_);
v_sz_288_ = lean_array_size(v_defs_283_);
v___x_289_ = ((size_t)0ULL);
v___x_253__overap_290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_278_, v___f_279_, v_sz_288_, v___x_289_, v_defs_283_);
lean_inc_ref(v___y_281_);
v___x_291_ = lean_apply_1(v___x_253__overap_290_, v___y_281_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_291_);
lean_ctor_set(v___x_285_, 0, v___x_287_);
v___x_293_ = v___x_285_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1___boxed(lean_object* v___x_296_, lean_object* v___f_297_, lean_object* v_s_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(v___x_296_, v___f_297_, v_s_298_, v___y_299_);
lean_dec_ref(v___y_299_);
return v_res_300_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0(void){
_start:
{
lean_object* v___x_301_; lean_object* v___f_302_; 
v___x_301_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot;
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_302_, 0, v___x_301_);
return v___f_302_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1(void){
_start:
{
lean_object* v___f_303_; lean_object* v___f_304_; 
v___f_303_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0, &l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_once, _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0___boxed), 3, 1);
lean_closure_set(v___f_304_, 0, v___f_303_);
return v___f_304_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2(void){
_start:
{
lean_object* v___f_305_; lean_object* v___x_306_; lean_object* v___f_307_; 
v___f_305_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1, &l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_once, _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1);
v___x_306_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10, &l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10_once, _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__10);
v___f_307_ = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1___boxed), 4, 2);
lean_closure_set(v___f_307_, 0, v___x_306_);
lean_closure_set(v___f_307_, 1, v___f_305_);
return v___f_307_;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot(void){
_start:
{
lean_object* v___f_308_; 
v___f_308_ = lean_obj_once(&l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2, &l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_once, _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2);
return v___f_308_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView_default___closed__0(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; 
v___x_309_ = lean_box(0);
v___x_310_ = l_Lean_Elab_instInhabitedModifiers_default;
v___x_311_ = lean_box(0);
v___x_312_ = 0;
v___x_313_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
lean_ctor_set(v___x_313_, 2, v___x_310_);
lean_ctor_set(v___x_313_, 3, v___x_311_);
lean_ctor_set(v___x_313_, 4, v___x_311_);
lean_ctor_set(v___x_313_, 5, v___x_309_);
lean_ctor_set(v___x_313_, 6, v___x_311_);
lean_ctor_set(v___x_313_, 7, v___x_309_);
lean_ctor_set(v___x_313_, 8, v___x_309_);
lean_ctor_set(v___x_313_, 9, v___x_309_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*10, v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView_default(void){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = lean_obj_once(&l_Lean_Elab_instInhabitedDefView_default___closed__0, &l_Lean_Elab_instInhabitedDefView_default___closed__0_once, _init_l_Lean_Elab_instInhabitedDefView_default___closed__0);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Elab_instInhabitedDefView_default;
return v___x_315_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(lean_object* v_as_319_, size_t v_i_320_, size_t v_stop_321_){
_start:
{
uint8_t v___x_322_; 
v___x_322_ = lean_usize_dec_eq(v_i_320_, v_stop_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v_name_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_323_ = lean_array_uget_borrowed(v_as_319_, v_i_320_);
v_name_324_ = lean_ctor_get(v___x_323_, 0);
v___x_325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1));
v___x_326_ = lean_name_eq(v_name_324_, v___x_325_);
if (v___x_326_ == 0)
{
size_t v___x_327_; size_t v___x_328_; 
v___x_327_ = ((size_t)1ULL);
v___x_328_ = lean_usize_add(v_i_320_, v___x_327_);
v_i_320_ = v___x_328_;
goto _start;
}
else
{
return v___x_326_;
}
}
else
{
uint8_t v___x_330_; 
v___x_330_ = 0;
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___boxed(lean_object* v_as_331_, lean_object* v_i_332_, lean_object* v_stop_333_){
_start:
{
size_t v_i_boxed_334_; size_t v_stop_boxed_335_; uint8_t v_res_336_; lean_object* v_r_337_; 
v_i_boxed_334_ = lean_unbox_usize(v_i_332_);
lean_dec(v_i_332_);
v_stop_boxed_335_ = lean_unbox_usize(v_stop_333_);
lean_dec(v_stop_333_);
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_as_331_, v_i_boxed_334_, v_stop_boxed_335_);
lean_dec_ref(v_as_331_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_isInstance(lean_object* v_view_338_){
_start:
{
lean_object* v_modifiers_339_; lean_object* v_attrs_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_modifiers_339_ = lean_ctor_get(v_view_338_, 2);
v_attrs_340_ = lean_ctor_get(v_modifiers_339_, 2);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_array_get_size(v_attrs_340_);
v___x_343_ = lean_nat_dec_lt(v___x_341_, v___x_342_);
if (v___x_343_ == 0)
{
return v___x_343_;
}
else
{
if (v___x_343_ == 0)
{
return v___x_343_;
}
else
{
size_t v___x_344_; size_t v___x_345_; uint8_t v___x_346_; 
v___x_344_ = ((size_t)0ULL);
v___x_345_ = lean_usize_of_nat(v___x_342_);
v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_attrs_340_, v___x_344_, v___x_345_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_isInstance___boxed(lean_object* v_view_347_){
_start:
{
uint8_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_Lean_Elab_DefView_isInstance(v_view_347_);
lean_dec_ref(v_view_347_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_markDefEq___lam__0(lean_object* v_x_353_){
_start:
{
lean_object* v_name_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_name_354_ = lean_ctor_get(v_x_353_, 0);
v___x_355_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___lam__0___closed__1));
v___x_356_ = lean_name_eq(v_name_354_, v___x_355_);
if (v___x_356_ == 0)
{
uint8_t v___x_357_; 
v___x_357_ = 1;
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = 0;
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_markDefEq___lam__0___boxed(lean_object* v_x_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Lean_Elab_DefView_markDefEq___lam__0(v_x_359_);
lean_dec_ref(v_x_359_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_markDefEq(lean_object* v_view_367_){
_start:
{
uint8_t v_kind_368_; lean_object* v_ref_369_; lean_object* v_headerRef_370_; lean_object* v_modifiers_371_; lean_object* v_declId_372_; lean_object* v_binders_373_; lean_object* v_type_x3f_374_; lean_object* v_value_375_; lean_object* v_docString_x3f_376_; lean_object* v_headerSnap_x3f_377_; lean_object* v_deriving_x3f_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_389_; 
v_kind_368_ = lean_ctor_get_uint8(v_view_367_, sizeof(void*)*10);
v_ref_369_ = lean_ctor_get(v_view_367_, 0);
v_headerRef_370_ = lean_ctor_get(v_view_367_, 1);
v_modifiers_371_ = lean_ctor_get(v_view_367_, 2);
v_declId_372_ = lean_ctor_get(v_view_367_, 3);
v_binders_373_ = lean_ctor_get(v_view_367_, 4);
v_type_x3f_374_ = lean_ctor_get(v_view_367_, 5);
v_value_375_ = lean_ctor_get(v_view_367_, 6);
v_docString_x3f_376_ = lean_ctor_get(v_view_367_, 7);
v_headerSnap_x3f_377_ = lean_ctor_get(v_view_367_, 8);
v_deriving_x3f_378_ = lean_ctor_get(v_view_367_, 9);
v_isSharedCheck_389_ = !lean_is_exclusive(v_view_367_);
if (v_isSharedCheck_389_ == 0)
{
v___x_380_ = v_view_367_;
v_isShared_381_ = v_isSharedCheck_389_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_deriving_x3f_378_);
lean_inc(v_headerSnap_x3f_377_);
lean_inc(v_docString_x3f_376_);
lean_inc(v_value_375_);
lean_inc(v_type_x3f_374_);
lean_inc(v_binders_373_);
lean_inc(v_declId_372_);
lean_inc(v_modifiers_371_);
lean_inc(v_headerRef_370_);
lean_inc(v_ref_369_);
lean_dec(v_view_367_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_389_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___f_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___f_382_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___closed__0));
v___x_383_ = l_Lean_Elab_Modifiers_filterAttrs(v_modifiers_371_, v___f_382_);
v___x_384_ = ((lean_object*)(l_Lean_Elab_DefView_markDefEq___closed__1));
v___x_385_ = l_Lean_Elab_Modifiers_addFirstAttr(v___x_383_, v___x_384_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 2, v___x_385_);
v___x_387_ = v___x_380_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_ref_369_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_headerRef_370_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v_declId_372_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_binders_373_);
lean_ctor_set(v_reuseFailAlloc_388_, 5, v_type_x3f_374_);
lean_ctor_set(v_reuseFailAlloc_388_, 6, v_value_375_);
lean_ctor_set(v_reuseFailAlloc_388_, 7, v_docString_x3f_376_);
lean_ctor_set(v_reuseFailAlloc_388_, 8, v_headerSnap_x3f_377_);
lean_ctor_set(v_reuseFailAlloc_388_, 9, v_deriving_x3f_378_);
lean_ctor_set_uint8(v_reuseFailAlloc_388_, sizeof(void*)*10, v_kind_368_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev(lean_object* v_modifiers_407_, lean_object* v_stx_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_fst_412_; lean_object* v_snd_413_; lean_object* v___x_414_; lean_object* v_modifiers_415_; lean_object* v___x_416_; lean_object* v_modifiers_417_; lean_object* v_docString_x3f_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_409_ = lean_unsigned_to_nat(2u);
v___x_410_ = l_Lean_Syntax_getArg(v_stx_408_, v___x_409_);
v___x_411_ = l_Lean_Elab_expandOptDeclSig(v___x_410_);
lean_dec(v___x_410_);
v_fst_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_fst_412_);
v_snd_413_ = lean_ctor_get(v___x_411_, 1);
lean_inc(v_snd_413_);
lean_dec_ref(v___x_411_);
v___x_414_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2));
v_modifiers_415_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_407_, v___x_414_);
v___x_416_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5));
v_modifiers_417_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_415_, v___x_416_);
v_docString_x3f_418_ = lean_ctor_get(v_modifiers_417_, 1);
lean_inc(v_docString_x3f_418_);
v___x_419_ = 5;
v___x_420_ = l_Lean_Syntax_getArgs(v_stx_408_);
v___x_421_ = lean_unsigned_to_nat(3u);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = l_Array_toSubarray___redArg(v___x_420_, v___x_422_, v___x_421_);
v___x_424_ = l_Subarray_copy___redArg(v___x_423_);
v___x_425_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_426_ = lean_box(2);
v___x_427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v___x_425_);
lean_ctor_set(v___x_427_, 2, v___x_424_);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = l_Lean_Syntax_getArg(v_stx_408_, v___x_428_);
v___x_430_ = l_Lean_Syntax_getArg(v_stx_408_, v___x_421_);
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_432_, 0, v_stx_408_);
lean_ctor_set(v___x_432_, 1, v___x_427_);
lean_ctor_set(v___x_432_, 2, v_modifiers_417_);
lean_ctor_set(v___x_432_, 3, v___x_429_);
lean_ctor_set(v___x_432_, 4, v_fst_412_);
lean_ctor_set(v___x_432_, 5, v_snd_413_);
lean_ctor_set(v___x_432_, 6, v___x_430_);
lean_ctor_set(v___x_432_, 7, v_docString_x3f_418_);
lean_ctor_set(v___x_432_, 8, v___x_431_);
lean_ctor_set(v___x_432_, 9, v___x_431_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*10, v___x_419_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfDef(lean_object* v_modifiers_433_, lean_object* v_stx_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___y_441_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_435_ = lean_unsigned_to_nat(2u);
v___x_436_ = l_Lean_Syntax_getArg(v_stx_434_, v___x_435_);
v___x_437_ = l_Lean_Elab_expandOptDeclSig(v___x_436_);
lean_dec(v___x_436_);
v_fst_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_fst_438_);
v_snd_439_ = lean_ctor_get(v___x_437_, 1);
lean_inc(v_snd_439_);
lean_dec_ref(v___x_437_);
v___x_457_ = lean_unsigned_to_nat(4u);
v___x_458_ = l_Lean_Syntax_getArg(v_stx_434_, v___x_457_);
v___x_459_ = l_Lean_Syntax_isNone(v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = l_Lean_Syntax_getArg(v___x_458_, v___x_460_);
lean_dec(v___x_458_);
v___x_462_ = l_Lean_Syntax_getSepArgs(v___x_461_);
lean_dec(v___x_461_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
v___y_441_ = v___x_463_;
goto v___jp_440_;
}
else
{
lean_object* v___x_464_; 
lean_dec(v___x_458_);
v___x_464_ = lean_box(0);
v___y_441_ = v___x_464_;
goto v___jp_440_;
}
v___jp_440_:
{
lean_object* v_docString_x3f_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_docString_x3f_442_ = lean_ctor_get(v_modifiers_433_, 1);
lean_inc(v_docString_x3f_442_);
v___x_443_ = 0;
v___x_444_ = l_Lean_Syntax_getArgs(v_stx_434_);
v___x_445_ = lean_unsigned_to_nat(3u);
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = l_Array_toSubarray___redArg(v___x_444_, v___x_446_, v___x_445_);
v___x_448_ = l_Subarray_copy___redArg(v___x_447_);
v___x_449_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_450_ = lean_box(2);
v___x_451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
lean_ctor_set(v___x_451_, 2, v___x_448_);
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = l_Lean_Syntax_getArg(v_stx_434_, v___x_452_);
v___x_454_ = l_Lean_Syntax_getArg(v_stx_434_, v___x_445_);
v___x_455_ = lean_box(0);
v___x_456_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_456_, 0, v_stx_434_);
lean_ctor_set(v___x_456_, 1, v___x_451_);
lean_ctor_set(v___x_456_, 2, v_modifiers_433_);
lean_ctor_set(v___x_456_, 3, v___x_453_);
lean_ctor_set(v___x_456_, 4, v_fst_438_);
lean_ctor_set(v___x_456_, 5, v_snd_439_);
lean_ctor_set(v___x_456_, 6, v___x_454_);
lean_ctor_set(v___x_456_, 7, v_docString_x3f_442_);
lean_ctor_set(v___x_456_, 8, v___x_455_);
lean_ctor_set(v___x_456_, 9, v___y_441_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*10, v___x_443_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem(lean_object* v_modifiers_465_, lean_object* v_stx_466_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v_docString_x3f_472_; uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_467_ = lean_unsigned_to_nat(2u);
v___x_468_ = l_Lean_Syntax_getArg(v_stx_466_, v___x_467_);
v___x_469_ = l_Lean_Elab_expandDeclSig(v___x_468_);
lean_dec(v___x_468_);
v_fst_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_fst_470_);
v_snd_471_ = lean_ctor_get(v___x_469_, 1);
lean_inc(v_snd_471_);
lean_dec_ref(v___x_469_);
v_docString_x3f_472_ = lean_ctor_get(v_modifiers_465_, 1);
lean_inc(v_docString_x3f_472_);
v___x_473_ = 2;
v___x_474_ = l_Lean_Syntax_getArgs(v_stx_466_);
v___x_475_ = lean_unsigned_to_nat(3u);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = l_Array_toSubarray___redArg(v___x_474_, v___x_476_, v___x_475_);
v___x_478_ = l_Subarray_copy___redArg(v___x_477_);
v___x_479_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_480_ = lean_box(2);
v___x_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
lean_ctor_set(v___x_481_, 2, v___x_478_);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = l_Lean_Syntax_getArg(v_stx_466_, v___x_482_);
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v_snd_471_);
v___x_485_ = l_Lean_Syntax_getArg(v_stx_466_, v___x_475_);
v___x_486_ = lean_box(0);
v___x_487_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_487_, 0, v_stx_466_);
lean_ctor_set(v___x_487_, 1, v___x_481_);
lean_ctor_set(v___x_487_, 2, v_modifiers_465_);
lean_ctor_set(v___x_487_, 3, v___x_483_);
lean_ctor_set(v___x_487_, 4, v_fst_470_);
lean_ctor_set(v___x_487_, 5, v___x_484_);
lean_ctor_set(v___x_487_, 6, v___x_485_);
lean_ctor_set(v___x_487_, 7, v_docString_x3f_472_);
lean_ctor_set(v___x_487_, 8, v___x_486_);
lean_ctor_set(v___x_487_, 9, v___x_486_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*10, v___x_473_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; lean_object* v_env_491_; lean_object* v___x_492_; lean_object* v_mainModule_493_; lean_object* v___x_494_; 
v___x_490_ = lean_st_ref_get(v___y_488_);
v_env_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc_ref(v_env_491_);
lean_dec(v___x_490_);
v___x_492_ = l_Lean_Environment_header(v_env_491_);
lean_dec_ref(v_env_491_);
v_mainModule_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_mainModule_493_);
lean_dec_ref(v___x_492_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v_mainModule_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg___boxed(lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_495_);
lean_dec(v___y_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___boxed(lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_505_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = l_Lean_maxRecDepthErrorMessage;
v___x_512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3);
v___x_514_ = l_Lean_MessageData_ofFormat(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4);
v___x_516_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2));
v___x_517_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v___x_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(lean_object* v_ref_518_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v_ref_518_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___boxed(lean_object* v_ref_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(lean_object* v_x_526_, lean_object* v___y_527_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; 
v_a_528_ = lean_ctor_get(v_x_526_, 0);
lean_inc(v_a_528_);
v___x_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_529_, 0, v_a_528_);
lean_ctor_set(v___x_529_, 1, v___y_527_);
return v___x_529_;
}
else
{
lean_object* v_a_530_; lean_object* v___x_531_; 
v_a_530_ = lean_ctor_get(v_x_526_, 0);
lean_inc(v_a_530_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_a_530_);
lean_ctor_set(v___x_531_, 1, v___y_527_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg___boxed(lean_object* v_x_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_532_, v___y_533_);
lean_dec_ref(v_x_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(lean_object* v_env_535_, lean_object* v_stx_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_535_, v_stx_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
if (lean_obj_tag(v_a_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_549_; 
v_a_541_ = lean_ctor_get(v___x_539_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v___x_539_, 0);
lean_dec(v_unused_550_);
v___x_543_ = v___x_539_;
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_box(0);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_a_541_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
else
{
lean_object* v_val_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_579_; 
v_val_551_ = lean_ctor_get(v_a_540_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_a_540_);
if (v_isSharedCheck_579_ == 0)
{
v___x_553_ = v_a_540_;
v_isShared_554_ = v_isSharedCheck_579_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_val_551_);
lean_dec(v_a_540_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_579_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_snd_555_; 
v_snd_555_ = lean_ctor_get(v_val_551_, 1);
lean_inc(v_snd_555_);
lean_dec(v_val_551_);
if (lean_obj_tag(v_snd_555_) == 0)
{
lean_object* v_a_556_; lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_565_; 
lean_del_object(v___x_553_);
v_a_556_ = lean_ctor_get(v___x_539_, 1);
lean_inc(v_a_556_);
lean_dec_ref_known(v___x_539_, 2);
v_a_557_ = lean_ctor_get(v_snd_555_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_snd_555_);
if (v_isSharedCheck_565_ == 0)
{
v___x_559_ = v_snd_555_;
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v_snd_555_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; 
v___x_563_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_562_, v_a_556_);
lean_dec_ref(v___x_562_);
return v___x_563_;
}
}
}
else
{
lean_object* v_a_566_; lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_578_; 
v_a_566_ = lean_ctor_get(v___x_539_, 1);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_539_, 2);
v_a_567_ = lean_ctor_get(v_snd_555_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_snd_555_);
if (v_isSharedCheck_578_ == 0)
{
v___x_569_ = v_snd_555_;
v_isShared_570_ = v_isSharedCheck_578_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v_snd_555_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_578_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v_a_567_);
v___x_572_ = v___x_553_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_577_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_572_);
v___x_574_ = v___x_569_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_576_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; 
v___x_575_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_574_, v_a_566_);
lean_dec_ref(v___x_574_);
return v___x_575_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_a_580_ = lean_ctor_get(v___x_539_, 0);
v_a_581_ = lean_ctor_get(v___x_539_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_539_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_inc(v_a_580_);
lean_dec(v___x_539_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_580_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed(lean_object* v_env_589_, lean_object* v_stx_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(v_env_589_, v_stx_590_, v___y_591_, v___y_592_);
lean_dec_ref(v___y_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(lean_object* v_env_594_, lean_object* v_currNamespace_595_, lean_object* v_openDecls_596_, lean_object* v_n_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = l_Lean_ResolveName_resolveNamespace(v_env_594_, v_currNamespace_595_, v_openDecls_596_, v_n_597_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___y_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed(lean_object* v_env_602_, lean_object* v_currNamespace_603_, lean_object* v_openDecls_604_, lean_object* v_n_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(v_env_602_, v_currNamespace_603_, v_openDecls_604_, v_n_605_, v___y_606_, v___y_607_);
lean_dec_ref(v___y_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(lean_object* v_currNamespace_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_currNamespace_609_);
lean_ctor_set(v___x_612_, 1, v___y_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(v_currNamespace_613_, v___y_614_, v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_616_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_box(0);
v___x_618_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___x_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg(){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___boxed(lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v_res_624_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_625_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_629_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
lean_ctor_set(v___x_631_, 2, v___x_630_);
lean_ctor_set(v___x_631_, 3, v___x_630_);
lean_ctor_set(v___x_631_, 4, v___x_629_);
lean_ctor_set(v___x_631_, 5, v___x_629_);
lean_ctor_set(v___x_631_, 6, v___x_629_);
lean_ctor_set(v___x_631_, 7, v___x_629_);
lean_ctor_set(v___x_631_, 8, v___x_629_);
lean_ctor_set(v___x_631_, 9, v___x_629_);
lean_ctor_set(v___x_631_, 10, v___x_629_);
lean_ctor_set(v___x_631_, 11, v___x_628_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_unsigned_to_nat(32u);
v___x_633_ = lean_mk_empty_array_with_capacity(v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_635_ = ((size_t)5ULL);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_unsigned_to_nat(32u);
v___x_638_ = lean_mk_empty_array_with_capacity(v___x_637_);
v___x_639_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3);
v___x_640_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_638_);
lean_ctor_set(v___x_640_, 2, v___x_636_);
lean_ctor_set(v___x_640_, 3, v___x_636_);
lean_ctor_set_usize(v___x_640_, 4, v___x_635_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_641_ = lean_box(1);
v___x_642_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4);
v___x_643_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
v___x_644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_642_);
lean_ctor_set(v___x_644_, 2, v___x_641_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(lean_object* v_msgData_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; lean_object* v_env_649_; uint8_t v___x_650_; lean_object* v_env_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_scopes_654_; lean_object* v___x_655_; lean_object* v_opts_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_648_ = lean_st_ref_get(v___y_646_);
v_env_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_env_649_);
lean_dec(v___x_648_);
v___x_650_ = 0;
v_env_651_ = l_Lean_Environment_setRecordingDeps(v_env_649_, v___x_650_);
v___x_652_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_653_ = lean_st_ref_get(v___y_646_);
v_scopes_654_ = lean_ctor_get(v___x_653_, 2);
lean_inc(v_scopes_654_);
lean_dec(v___x_653_);
v___x_655_ = l_List_head_x21___redArg(v___x_652_, v_scopes_654_);
lean_dec(v_scopes_654_);
v_opts_656_ = lean_ctor_get(v___x_655_, 1);
lean_inc_ref(v_opts_656_);
lean_dec(v___x_655_);
v___x_657_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2);
v___x_658_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5);
v___x_659_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_659_, 0, v_env_651_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
lean_ctor_set(v___x_659_, 2, v___x_658_);
lean_ctor_set(v___x_659_, 3, v_opts_656_);
v___x_660_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v_msgData_645_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___boxed(lean_object* v_msgData_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_662_, v___y_663_);
lean_dec(v___y_663_);
return v_res_665_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0(void){
_start:
{
lean_object* v___x_666_; double v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_float_of_nat(v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(lean_object* v_cls_671_, lean_object* v_msg_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Elab_Command_getRef___redArg(v___y_673_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_727_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_672_, v___y_674_);
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_727_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_727_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_727_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v_traceState_684_; lean_object* v_env_685_; lean_object* v_messages_686_; lean_object* v_scopes_687_; lean_object* v_usedQuotCtxts_688_; lean_object* v_nextMacroScope_689_; lean_object* v_maxRecDepth_690_; lean_object* v_ngen_691_; lean_object* v_auxDeclNGen_692_; lean_object* v_infoState_693_; lean_object* v_snapshotTasks_694_; lean_object* v_prevLinterStates_695_; lean_object* v_codeQualityEntryTasks_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_726_; 
v___x_683_ = lean_st_ref_take(v___y_674_);
v_traceState_684_ = lean_ctor_get(v___x_683_, 9);
v_env_685_ = lean_ctor_get(v___x_683_, 0);
v_messages_686_ = lean_ctor_get(v___x_683_, 1);
v_scopes_687_ = lean_ctor_get(v___x_683_, 2);
v_usedQuotCtxts_688_ = lean_ctor_get(v___x_683_, 3);
v_nextMacroScope_689_ = lean_ctor_get(v___x_683_, 4);
v_maxRecDepth_690_ = lean_ctor_get(v___x_683_, 5);
v_ngen_691_ = lean_ctor_get(v___x_683_, 6);
v_auxDeclNGen_692_ = lean_ctor_get(v___x_683_, 7);
v_infoState_693_ = lean_ctor_get(v___x_683_, 8);
v_snapshotTasks_694_ = lean_ctor_get(v___x_683_, 10);
v_prevLinterStates_695_ = lean_ctor_get(v___x_683_, 11);
v_codeQualityEntryTasks_696_ = lean_ctor_get(v___x_683_, 12);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_726_ == 0)
{
v___x_698_ = v___x_683_;
v_isShared_699_ = v_isSharedCheck_726_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_codeQualityEntryTasks_696_);
lean_inc(v_prevLinterStates_695_);
lean_inc(v_snapshotTasks_694_);
lean_inc(v_traceState_684_);
lean_inc(v_infoState_693_);
lean_inc(v_auxDeclNGen_692_);
lean_inc(v_ngen_691_);
lean_inc(v_maxRecDepth_690_);
lean_inc(v_nextMacroScope_689_);
lean_inc(v_usedQuotCtxts_688_);
lean_inc(v_scopes_687_);
lean_inc(v_messages_686_);
lean_inc(v_env_685_);
lean_dec(v___x_683_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_726_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
uint64_t v_tid_700_; lean_object* v_traces_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_725_; 
v_tid_700_ = lean_ctor_get_uint64(v_traceState_684_, sizeof(void*)*1);
v_traces_701_ = lean_ctor_get(v_traceState_684_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_traceState_684_);
if (v_isSharedCheck_725_ == 0)
{
v___x_703_ = v_traceState_684_;
v_isShared_704_ = v_isSharedCheck_725_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_traces_701_);
lean_dec(v_traceState_684_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_725_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; double v___x_707_; uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_705_ = lean_box(0);
v___x_706_ = lean_box(0);
v___x_707_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0);
v___x_708_ = 0;
v___x_709_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1));
v___x_710_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_710_, 0, v_cls_671_);
lean_ctor_set(v___x_710_, 1, v___x_706_);
lean_ctor_set(v___x_710_, 2, v___x_709_);
lean_ctor_set_float(v___x_710_, sizeof(void*)*3, v___x_707_);
lean_ctor_set_float(v___x_710_, sizeof(void*)*3 + 8, v___x_707_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*3 + 16, v___x_708_);
v___x_711_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2));
v___x_712_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v_a_679_);
lean_ctor_set(v___x_712_, 2, v___x_711_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_a_677_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_PersistentArray_push___redArg(v_traces_701_, v___x_713_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_714_);
v___x_716_ = v___x_703_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_714_);
lean_ctor_set_uint64(v_reuseFailAlloc_724_, sizeof(void*)*1, v_tid_700_);
v___x_716_ = v_reuseFailAlloc_724_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 9, v___x_716_);
v___x_718_ = v___x_698_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_env_685_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_messages_686_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_scopes_687_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_usedQuotCtxts_688_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_nextMacroScope_689_);
lean_ctor_set(v_reuseFailAlloc_723_, 5, v_maxRecDepth_690_);
lean_ctor_set(v_reuseFailAlloc_723_, 6, v_ngen_691_);
lean_ctor_set(v_reuseFailAlloc_723_, 7, v_auxDeclNGen_692_);
lean_ctor_set(v_reuseFailAlloc_723_, 8, v_infoState_693_);
lean_ctor_set(v_reuseFailAlloc_723_, 9, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_723_, 10, v_snapshotTasks_694_);
lean_ctor_set(v_reuseFailAlloc_723_, 11, v_prevLinterStates_695_);
lean_ctor_set(v_reuseFailAlloc_723_, 12, v_codeQualityEntryTasks_696_);
v___x_718_ = v_reuseFailAlloc_723_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_st_ref_put(v___y_674_, v___x_718_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_705_);
v___x_721_ = v___x_681_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_705_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v_msg_672_);
lean_dec(v_cls_671_);
v_a_728_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_676_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_676_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___boxed(lean_object* v_cls_736_, lean_object* v_msg_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_cls_736_, v_msg_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___lam__0(lean_object* v___x_742_, lean_object* v_entry_743_, lean_object* v_s_744_){
_start:
{
lean_object* v_addEntryFn_745_; lean_object* v_importedEntries_746_; lean_object* v_state_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
v_addEntryFn_745_ = lean_ctor_get(v___x_742_, 3);
lean_inc(v_addEntryFn_745_);
lean_dec_ref(v___x_742_);
v_importedEntries_746_ = lean_ctor_get(v_s_744_, 0);
v_state_747_ = lean_ctor_get(v_s_744_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_s_744_);
if (v_isSharedCheck_755_ == 0)
{
v___x_749_ = v_s_744_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_state_747_);
lean_inc(v_importedEntries_746_);
lean_dec(v_s_744_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_state_751_; lean_object* v___x_753_; 
v_state_751_ = lean_apply_2(v_addEntryFn_745_, v_state_747_, v_entry_743_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v_state_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_importedEntries_746_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_state_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(lean_object* v_keys_756_, lean_object* v_i_757_, lean_object* v_k_758_){
_start:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_array_get_size(v_keys_756_);
v___x_760_ = lean_nat_dec_lt(v_i_757_, v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v_i_757_);
return v___x_760_;
}
else
{
lean_object* v_k_x27_761_; uint8_t v___x_762_; 
v_k_x27_761_ = lean_array_fget_borrowed(v_keys_756_, v_i_757_);
v___x_762_ = l_Lean_instBEqExtraModUse_beq(v_k_758_, v_k_x27_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v_i_757_, v___x_763_);
lean_dec(v_i_757_);
v_i_757_ = v___x_764_;
goto _start;
}
else
{
lean_dec(v_i_757_);
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg___boxed(lean_object* v_keys_766_, lean_object* v_i_767_, lean_object* v_k_768_){
_start:
{
uint8_t v_res_769_; lean_object* v_r_770_; 
v_res_769_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_766_, v_i_767_, v_k_768_);
lean_dec_ref(v_k_768_);
lean_dec_ref(v_keys_766_);
v_r_770_ = lean_box(v_res_769_);
return v_r_770_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(lean_object* v_x_771_, size_t v_x_772_, lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_771_) == 0)
{
lean_object* v_es_774_; lean_object* v___x_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v_j_778_; lean_object* v___x_779_; 
v_es_774_ = lean_ctor_get(v_x_771_, 0);
v___x_775_ = lean_box(2);
v___x_776_ = ((size_t)31ULL);
v___x_777_ = lean_usize_land(v_x_772_, v___x_776_);
v_j_778_ = lean_usize_to_nat(v___x_777_);
v___x_779_ = lean_array_get_borrowed(v___x_775_, v_es_774_, v_j_778_);
lean_dec(v_j_778_);
switch(lean_obj_tag(v___x_779_))
{
case 0:
{
lean_object* v_key_780_; uint8_t v___x_781_; 
v_key_780_ = lean_ctor_get(v___x_779_, 0);
v___x_781_ = l_Lean_instBEqExtraModUse_beq(v_x_773_, v_key_780_);
return v___x_781_;
}
case 1:
{
lean_object* v_node_782_; size_t v___x_783_; size_t v___x_784_; 
v_node_782_ = lean_ctor_get(v___x_779_, 0);
v___x_783_ = ((size_t)5ULL);
v___x_784_ = lean_usize_shift_right(v_x_772_, v___x_783_);
v_x_771_ = v_node_782_;
v_x_772_ = v___x_784_;
goto _start;
}
default: 
{
uint8_t v___x_786_; 
v___x_786_ = 0;
return v___x_786_;
}
}
}
else
{
lean_object* v_ks_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_ks_787_ = lean_ctor_get(v_x_771_, 0);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_ks_787_, v___x_788_, v_x_773_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
size_t v_x_16715__boxed_793_; uint8_t v_res_794_; lean_object* v_r_795_; 
v_x_16715__boxed_793_ = lean_unbox_usize(v_x_791_);
lean_dec(v_x_791_);
v_res_794_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_790_, v_x_16715__boxed_793_, v_x_792_);
lean_dec_ref(v_x_792_);
lean_dec_ref(v_x_790_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
uint64_t v___x_798_; size_t v___x_799_; uint8_t v___x_800_; 
v___x_798_ = l_Lean_instHashableExtraModUse_hash(v_x_797_);
v___x_799_ = lean_uint64_to_usize(v___x_798_);
v___x_800_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_796_, v___x_799_, v_x_797_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
uint8_t v_res_803_; lean_object* v_r_804_; 
v_res_803_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_801_, v_x_802_);
lean_dec_ref(v_x_802_);
lean_dec_ref(v_x_801_);
v_r_804_ = lean_box(v_res_803_);
return v_r_804_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_805_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3));
v___x_811_ = l_Lean_stringToMessageData(v___x_810_);
return v___x_811_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5));
v___x_814_ = l_Lean_stringToMessageData(v___x_813_);
return v___x_814_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1));
v___x_816_ = l_Lean_stringToMessageData(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_cls_820_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2));
v___x_821_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9));
v___x_822_ = l_Lean_Name_append(v___x_821_, v_cls_820_);
return v___x_822_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(lean_object* v_mod_833_, uint8_t v_isMeta_834_, lean_object* v_hint_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_env_860_; uint8_t v_isExporting_861_; lean_object* v_entry_862_; lean_object* v___x_863_; lean_object* v_env_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_858_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0);
v___x_859_ = lean_st_ref_get(v___y_837_);
v_env_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc_ref(v_env_860_);
lean_dec(v___x_859_);
v_isExporting_861_ = lean_ctor_get_uint8(v_env_860_, sizeof(void*)*13);
lean_dec_ref(v_env_860_);
lean_inc(v_mod_833_);
v_entry_862_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_862_, 0, v_mod_833_);
lean_ctor_set_uint8(v_entry_862_, sizeof(void*)*1, v_isExporting_861_);
lean_ctor_set_uint8(v_entry_862_, sizeof(void*)*1 + 1, v_isMeta_834_);
v___x_863_ = lean_st_ref_get(v___y_837_);
v_env_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc_ref(v_env_864_);
lean_dec(v___x_863_);
v___x_865_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_866_ = lean_box(1);
v___x_867_ = lean_box(0);
v___x_868_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_858_, v___x_865_, v_env_864_, v___x_866_, v___x_867_);
v___x_869_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v___x_868_, v_entry_862_);
lean_dec(v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___f_870_; uint8_t v___x_871_; lean_object* v___y_873_; lean_object* v_cls_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v_scopes_919_; lean_object* v___x_920_; lean_object* v_opts_921_; uint8_t v_hasTrace_922_; 
v___f_870_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_870_, 0, v___x_865_);
lean_closure_set(v___f_870_, 1, v_entry_862_);
v___x_871_ = 1;
v_cls_895_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2));
v___x_896_ = l_Lean_inheritedTraceOptions;
v___x_897_ = lean_st_ref_get(v___x_896_);
v___x_898_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_899_ = lean_st_ref_get(v___y_837_);
v_scopes_919_ = lean_ctor_get(v___x_899_, 2);
lean_inc(v_scopes_919_);
lean_dec(v___x_899_);
v___x_920_ = l_List_head_x21___redArg(v___x_898_, v_scopes_919_);
lean_dec(v_scopes_919_);
v_opts_921_ = lean_ctor_get(v___x_920_, 1);
lean_inc_ref(v_opts_921_);
lean_dec(v___x_920_);
v_hasTrace_922_ = lean_ctor_get_uint8(v_opts_921_, sizeof(void*)*1);
if (v_hasTrace_922_ == 0)
{
lean_dec_ref(v_opts_921_);
lean_dec(v___x_897_);
lean_dec(v_hint_835_);
lean_dec(v_mod_833_);
v___y_873_ = v___y_837_;
goto v___jp_872_;
}
else
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10);
v___x_924_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_897_, v_opts_921_, v___x_923_);
lean_dec_ref(v_opts_921_);
lean_dec(v___x_897_);
if (v___x_924_ == 0)
{
lean_dec(v_hint_835_);
lean_dec(v_mod_833_);
v___y_873_ = v___y_837_;
goto v___jp_872_;
}
else
{
lean_object* v___x_925_; lean_object* v___y_927_; 
v___x_925_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12);
if (v_isExporting_861_ == 0)
{
lean_object* v___x_934_; 
v___x_934_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17));
v___y_927_ = v___x_934_;
goto v___jp_926_;
}
else
{
lean_object* v___x_935_; 
v___x_935_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18));
v___y_927_ = v___x_935_;
goto v___jp_926_;
}
v___jp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_inc_ref(v___y_927_);
v___x_928_ = l_Lean_stringToMessageData(v___y_927_);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_925_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
if (v_isMeta_834_ == 0)
{
lean_object* v___x_932_; 
v___x_932_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15));
v___y_906_ = v___x_931_;
v___y_907_ = v___x_932_;
goto v___jp_905_;
}
else
{
lean_object* v___x_933_; 
v___x_933_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16));
v___y_906_ = v___x_931_;
v___y_907_ = v___x_933_;
goto v___jp_905_;
}
}
}
}
v___jp_872_:
{
lean_object* v___x_874_; lean_object* v_toEnvExtension_875_; lean_object* v_env_876_; lean_object* v_messages_877_; lean_object* v_scopes_878_; lean_object* v_usedQuotCtxts_879_; lean_object* v_nextMacroScope_880_; lean_object* v_maxRecDepth_881_; lean_object* v_ngen_882_; lean_object* v_auxDeclNGen_883_; lean_object* v_infoState_884_; lean_object* v_traceState_885_; lean_object* v_snapshotTasks_886_; lean_object* v_prevLinterStates_887_; lean_object* v_codeQualityEntryTasks_888_; lean_object* v_asyncMode_889_; uint8_t v_logWrites_890_; lean_object* v___x_891_; 
v___x_874_ = lean_st_ref_take(v___y_873_);
v_toEnvExtension_875_ = lean_ctor_get(v___x_865_, 0);
v_env_876_ = lean_ctor_get(v___x_874_, 0);
lean_inc_ref(v_env_876_);
v_messages_877_ = lean_ctor_get(v___x_874_, 1);
lean_inc_ref(v_messages_877_);
v_scopes_878_ = lean_ctor_get(v___x_874_, 2);
lean_inc(v_scopes_878_);
v_usedQuotCtxts_879_ = lean_ctor_get(v___x_874_, 3);
lean_inc(v_usedQuotCtxts_879_);
v_nextMacroScope_880_ = lean_ctor_get(v___x_874_, 4);
lean_inc(v_nextMacroScope_880_);
v_maxRecDepth_881_ = lean_ctor_get(v___x_874_, 5);
lean_inc(v_maxRecDepth_881_);
v_ngen_882_ = lean_ctor_get(v___x_874_, 6);
lean_inc_ref(v_ngen_882_);
v_auxDeclNGen_883_ = lean_ctor_get(v___x_874_, 7);
lean_inc_ref(v_auxDeclNGen_883_);
v_infoState_884_ = lean_ctor_get(v___x_874_, 8);
lean_inc_ref(v_infoState_884_);
v_traceState_885_ = lean_ctor_get(v___x_874_, 9);
lean_inc_ref(v_traceState_885_);
v_snapshotTasks_886_ = lean_ctor_get(v___x_874_, 10);
lean_inc_ref(v_snapshotTasks_886_);
v_prevLinterStates_887_ = lean_ctor_get(v___x_874_, 11);
lean_inc(v_prevLinterStates_887_);
v_codeQualityEntryTasks_888_ = lean_ctor_get(v___x_874_, 12);
lean_inc_ref(v_codeQualityEntryTasks_888_);
lean_dec(v___x_874_);
v_asyncMode_889_ = lean_ctor_get(v_toEnvExtension_875_, 2);
v_logWrites_890_ = lean_ctor_get_uint8(v_toEnvExtension_875_, sizeof(void*)*6);
v___x_891_ = lean_box(0);
if (v_logWrites_890_ == 0)
{
lean_object* v___x_892_; 
lean_inc_ref(v_toEnvExtension_875_);
v___x_892_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_875_, v_env_876_, v___f_870_, v_asyncMode_889_, v___x_867_, v___x_871_);
v___y_840_ = v_traceState_885_;
v___y_841_ = v_prevLinterStates_887_;
v___y_842_ = v___x_891_;
v___y_843_ = v_messages_877_;
v___y_844_ = v_snapshotTasks_886_;
v___y_845_ = v_ngen_882_;
v___y_846_ = v_usedQuotCtxts_879_;
v___y_847_ = v_nextMacroScope_880_;
v___y_848_ = v_scopes_878_;
v___y_849_ = v_codeQualityEntryTasks_888_;
v___y_850_ = v_maxRecDepth_881_;
v___y_851_ = v___y_873_;
v___y_852_ = v_auxDeclNGen_883_;
v___y_853_ = v_infoState_884_;
v___y_854_ = v___x_892_;
goto v___jp_839_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_inc_ref_n(v_toEnvExtension_875_, 2);
v___x_893_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_875_, v_env_876_);
lean_dec_ref(v_env_876_);
v___x_894_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_875_, v___x_893_, v___f_870_, v_asyncMode_889_, v___x_867_, v___x_871_);
v___y_840_ = v_traceState_885_;
v___y_841_ = v_prevLinterStates_887_;
v___y_842_ = v___x_891_;
v___y_843_ = v_messages_877_;
v___y_844_ = v_snapshotTasks_886_;
v___y_845_ = v_ngen_882_;
v___y_846_ = v_usedQuotCtxts_879_;
v___y_847_ = v_nextMacroScope_880_;
v___y_848_ = v_scopes_878_;
v___y_849_ = v_codeQualityEntryTasks_888_;
v___y_850_ = v_maxRecDepth_881_;
v___y_851_ = v___y_873_;
v___y_852_ = v_auxDeclNGen_883_;
v___y_853_ = v_infoState_884_;
v___y_854_ = v___x_894_;
goto v___jp_839_;
}
}
v___jp_900_:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___y_901_);
lean_ctor_set(v___x_903_, 1, v___y_902_);
v___x_904_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_cls_895_, v___x_903_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_dec_ref_known(v___x_904_, 1);
v___y_873_ = v___y_837_;
goto v___jp_872_;
}
else
{
lean_dec_ref(v___f_870_);
return v___x_904_;
}
}
v___jp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
lean_inc_ref(v___y_907_);
v___x_908_ = l_Lean_stringToMessageData(v___y_907_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___y_906_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l_Lean_MessageData_ofName(v_mod_833_);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Lean_Name_isAnonymous(v_hint_835_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6);
v___x_916_ = l_Lean_MessageData_ofName(v_hint_835_);
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___y_901_ = v___x_913_;
v___y_902_ = v___x_917_;
goto v___jp_900_;
}
else
{
lean_object* v___x_918_; 
lean_dec(v_hint_835_);
v___x_918_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7);
v___y_901_ = v___x_913_;
v___y_902_ = v___x_918_;
goto v___jp_900_;
}
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec_ref_known(v_entry_862_, 1);
lean_dec(v_hint_835_);
lean_dec(v_mod_833_);
v___x_936_ = lean_box(0);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
v___jp_839_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_855_, 0, v___y_854_);
lean_ctor_set(v___x_855_, 1, v___y_843_);
lean_ctor_set(v___x_855_, 2, v___y_848_);
lean_ctor_set(v___x_855_, 3, v___y_846_);
lean_ctor_set(v___x_855_, 4, v___y_847_);
lean_ctor_set(v___x_855_, 5, v___y_850_);
lean_ctor_set(v___x_855_, 6, v___y_845_);
lean_ctor_set(v___x_855_, 7, v___y_852_);
lean_ctor_set(v___x_855_, 8, v___y_853_);
lean_ctor_set(v___x_855_, 9, v___y_840_);
lean_ctor_set(v___x_855_, 10, v___y_844_);
lean_ctor_set(v___x_855_, 11, v___y_841_);
lean_ctor_set(v___x_855_, 12, v___y_849_);
v___x_856_ = lean_st_ref_put(v___y_851_, v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___y_842_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___boxed(lean_object* v_mod_938_, lean_object* v_isMeta_939_, lean_object* v_hint_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v_isMeta_boxed_944_; lean_object* v_res_945_; 
v_isMeta_boxed_944_ = lean_unbox(v_isMeta_939_);
v_res_945_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_mod_938_, v_isMeta_boxed_944_, v_hint_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(lean_object* v___x_946_, lean_object* v_declName_947_, lean_object* v_as_948_, size_t v_sz_949_, size_t v_i_950_, lean_object* v_b_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = lean_usize_dec_lt(v_i_950_, v_sz_949_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec(v_declName_947_);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v_b_951_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v_modules_958_; lean_object* v___x_959_; lean_object* v_a_960_; lean_object* v___x_961_; lean_object* v_toImport_962_; lean_object* v_module_963_; lean_object* v___x_964_; uint8_t v___x_965_; lean_object* v___x_966_; 
v___x_957_ = l_Lean_Environment_header(v___x_946_);
v_modules_958_ = lean_ctor_get(v___x_957_, 3);
lean_inc_ref(v_modules_958_);
lean_dec_ref(v___x_957_);
v___x_959_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_960_ = lean_array_uget_borrowed(v_as_948_, v_i_950_);
v___x_961_ = lean_array_get(v___x_959_, v_modules_958_, v_a_960_);
lean_dec_ref(v_modules_958_);
v_toImport_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc_ref(v_toImport_962_);
lean_dec(v___x_961_);
v_module_963_ = lean_ctor_get(v_toImport_962_, 0);
lean_inc(v_module_963_);
lean_dec_ref(v_toImport_962_);
v___x_964_ = lean_box(0);
v___x_965_ = 0;
lean_inc(v_declName_947_);
v___x_966_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_963_, v___x_965_, v_declName_947_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_966_) == 0)
{
size_t v___x_967_; size_t v___x_968_; 
lean_dec_ref_known(v___x_966_, 1);
v___x_967_ = ((size_t)1ULL);
v___x_968_ = lean_usize_add(v_i_950_, v___x_967_);
v_i_950_ = v___x_968_;
v_b_951_ = v___x_964_;
goto _start;
}
else
{
lean_dec(v_declName_947_);
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___boxed(lean_object* v___x_970_, lean_object* v_declName_971_, lean_object* v_as_972_, lean_object* v_sz_973_, lean_object* v_i_974_, lean_object* v_b_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
size_t v_sz_boxed_979_; size_t v_i_boxed_980_; lean_object* v_res_981_; 
v_sz_boxed_979_ = lean_unbox_usize(v_sz_973_);
lean_dec(v_sz_973_);
v_i_boxed_980_ = lean_unbox_usize(v_i_974_);
lean_dec(v_i_974_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v___x_970_, v_declName_971_, v_as_972_, v_sz_boxed_979_, v_i_boxed_980_, v_b_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec_ref(v_as_972_);
lean_dec_ref(v___x_970_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_a_982_, lean_object* v_x_983_){
_start:
{
if (lean_obj_tag(v_x_983_) == 0)
{
lean_object* v___x_984_; 
v___x_984_ = lean_box(0);
return v___x_984_;
}
else
{
lean_object* v_key_985_; lean_object* v_value_986_; lean_object* v_tail_987_; uint8_t v___x_988_; 
v_key_985_ = lean_ctor_get(v_x_983_, 0);
v_value_986_ = lean_ctor_get(v_x_983_, 1);
v_tail_987_ = lean_ctor_get(v_x_983_, 2);
v___x_988_ = lean_name_eq(v_key_985_, v_a_982_);
if (v___x_988_ == 0)
{
v_x_983_ = v_tail_987_;
goto _start;
}
else
{
lean_object* v___x_990_; 
lean_inc(v_value_986_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v_value_986_);
return v___x_990_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_a_991_, lean_object* v_x_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_991_, v_x_992_);
lean_dec(v_x_992_);
lean_dec(v_a_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(lean_object* v_m_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_buckets_996_; lean_object* v___x_997_; uint64_t v___y_999_; 
v_buckets_996_ = lean_ctor_get(v_m_994_, 1);
v___x_997_ = lean_array_get_size(v_buckets_996_);
if (lean_obj_tag(v_a_995_) == 0)
{
uint64_t v___x_1013_; 
v___x_1013_ = 1723ULL;
v___y_999_ = v___x_1013_;
goto v___jp_998_;
}
else
{
uint64_t v_hash_1014_; 
v_hash_1014_ = lean_ctor_get_uint64(v_a_995_, sizeof(void*)*2);
v___y_999_ = v_hash_1014_;
goto v___jp_998_;
}
v___jp_998_:
{
uint64_t v___x_1000_; uint64_t v___x_1001_; uint64_t v_fold_1002_; uint64_t v___x_1003_; uint64_t v___x_1004_; uint64_t v___x_1005_; size_t v___x_1006_; size_t v___x_1007_; size_t v___x_1008_; size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1000_ = 32ULL;
v___x_1001_ = lean_uint64_shift_right(v___y_999_, v___x_1000_);
v_fold_1002_ = lean_uint64_xor(v___y_999_, v___x_1001_);
v___x_1003_ = 16ULL;
v___x_1004_ = lean_uint64_shift_right(v_fold_1002_, v___x_1003_);
v___x_1005_ = lean_uint64_xor(v_fold_1002_, v___x_1004_);
v___x_1006_ = lean_uint64_to_usize(v___x_1005_);
v___x_1007_ = lean_usize_of_nat(v___x_997_);
v___x_1008_ = ((size_t)1ULL);
v___x_1009_ = lean_usize_sub(v___x_1007_, v___x_1008_);
v___x_1010_ = lean_usize_land(v___x_1006_, v___x_1009_);
v___x_1011_ = lean_array_uget_borrowed(v_buckets_996_, v___x_1010_);
v___x_1012_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_995_, v___x_1011_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_m_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_m_1015_);
return v_res_1017_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(lean_object* v_declName_1021_, uint8_t v_isMeta_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v_env_1031_; lean_object* v___y_1033_; lean_object* v___x_1046_; 
v___x_1026_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0);
v___x_1027_ = lean_st_ref_get(v___y_1024_);
v_env_1031_ = lean_ctor_get(v___x_1027_, 0);
lean_inc_ref(v_env_1031_);
lean_dec(v___x_1027_);
v___x_1046_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1031_, v_declName_1021_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_dec_ref(v_env_1031_);
lean_dec(v_declName_1021_);
goto v___jp_1028_;
}
else
{
lean_object* v_val_1047_; lean_object* v___x_1048_; lean_object* v_modules_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_val_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_val_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = l_Lean_Environment_header(v_env_1031_);
v_modules_1049_ = lean_ctor_get(v___x_1048_, 3);
lean_inc_ref(v_modules_1049_);
lean_dec_ref(v___x_1048_);
v___x_1050_ = lean_array_get_size(v_modules_1049_);
v___x_1051_ = lean_nat_dec_lt(v_val_1047_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_dec_ref(v_modules_1049_);
lean_dec(v_val_1047_);
lean_dec_ref(v_env_1031_);
lean_dec(v_declName_1021_);
goto v___jp_1028_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___y_1055_; 
v___x_1052_ = lean_array_fget(v_modules_1049_, v_val_1047_);
lean_dec(v_val_1047_);
lean_dec_ref(v_modules_1049_);
v___x_1053_ = lean_st_ref_get(v___y_1024_);
if (v_isMeta_1022_ == 0)
{
lean_dec(v___x_1053_);
v___y_1055_ = v_isMeta_1022_;
goto v___jp_1054_;
}
else
{
lean_object* v_env_1066_; uint8_t v___x_1067_; 
v_env_1066_ = lean_ctor_get(v___x_1053_, 0);
lean_inc_ref(v_env_1066_);
lean_dec(v___x_1053_);
lean_inc(v_declName_1021_);
v___x_1067_ = l_Lean_isMarkedMeta(v_env_1066_, v_declName_1021_);
if (v___x_1067_ == 0)
{
v___y_1055_ = v_isMeta_1022_;
goto v___jp_1054_;
}
else
{
uint8_t v___x_1068_; 
v___x_1068_ = 0;
v___y_1055_ = v___x_1068_;
goto v___jp_1054_;
}
}
v___jp_1054_:
{
lean_object* v_toImport_1056_; lean_object* v_module_1057_; lean_object* v___x_1058_; 
v_toImport_1056_ = lean_ctor_get(v___x_1052_, 0);
lean_inc_ref(v_toImport_1056_);
lean_dec(v___x_1052_);
v_module_1057_ = lean_ctor_get(v_toImport_1056_, 0);
lean_inc(v_module_1057_);
lean_dec_ref(v_toImport_1056_);
lean_inc(v_declName_1021_);
v___x_1058_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_1057_, v___y_1055_, v_declName_1021_, v___y_1023_, v___y_1024_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_dec_ref_known(v___x_1058_, 1);
v___x_1059_ = l_Lean_indirectModUseExt;
v___x_1060_ = lean_box(1);
v___x_1061_ = lean_box(0);
lean_inc_ref(v_env_1031_);
v___x_1062_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1026_, v___x_1059_, v_env_1031_, v___x_1060_, v___x_1061_);
v___x_1063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v___x_1062_, v_declName_1021_);
lean_dec(v___x_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1));
v___y_1033_ = v___x_1064_;
goto v___jp_1032_;
}
else
{
lean_object* v_val_1065_; 
v_val_1065_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_val_1065_);
lean_dec_ref_known(v___x_1063_, 1);
v___y_1033_ = v_val_1065_;
goto v___jp_1032_;
}
}
else
{
lean_dec_ref(v_env_1031_);
lean_dec(v_declName_1021_);
return v___x_1058_;
}
}
}
}
v___jp_1028_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
v___jp_1032_:
{
lean_object* v___x_1034_; size_t v_sz_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
v___x_1034_ = lean_box(0);
v_sz_1035_ = lean_array_size(v___y_1033_);
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v_env_1031_, v_declName_1021_, v___y_1033_, v_sz_1035_, v___x_1036_, v___x_1034_, v___y_1023_, v___y_1024_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_env_1031_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v___x_1037_, 0);
lean_dec(v_unused_1045_);
v___x_1039_ = v___x_1037_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_dec(v___x_1037_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1034_);
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1034_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___boxed(lean_object* v_declName_1069_, lean_object* v_isMeta_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
uint8_t v_isMeta_boxed_1074_; lean_object* v_res_1075_; 
v_isMeta_boxed_1074_ = lean_unbox(v_isMeta_1070_);
v_res_1075_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_declName_1069_, v_isMeta_boxed_1074_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(lean_object* v_as_x27_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
if (lean_obj_tag(v_as_x27_1076_) == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_b_1077_);
return v___x_1081_;
}
else
{
lean_object* v_head_1082_; lean_object* v_tail_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; 
v_head_1082_ = lean_ctor_get(v_as_x27_1076_, 0);
v_tail_1083_ = lean_ctor_get(v_as_x27_1076_, 1);
v___x_1084_ = lean_box(0);
v___x_1085_ = 1;
lean_inc(v_head_1082_);
v___x_1086_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_head_1082_, v___x_1085_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_dec_ref_known(v___x_1086_, 1);
v_as_x27_1076_ = v_tail_1083_;
v_b_1077_ = v___x_1084_;
goto _start;
}
else
{
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg___boxed(lean_object* v_as_x27_1088_, lean_object* v_b_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_1088_, v_b_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v_as_x27_1088_);
return v_res_1093_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(lean_object* v_opts_1094_, lean_object* v_opt_1095_){
_start:
{
lean_object* v_name_1096_; lean_object* v_defValue_1097_; lean_object* v_map_1098_; lean_object* v___x_1099_; 
v_name_1096_ = lean_ctor_get(v_opt_1095_, 0);
v_defValue_1097_ = lean_ctor_get(v_opt_1095_, 1);
v_map_1098_ = lean_ctor_get(v_opts_1094_, 0);
v___x_1099_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1098_, v_name_1096_);
if (lean_obj_tag(v___x_1099_) == 0)
{
uint8_t v___x_1100_; 
v___x_1100_ = lean_unbox(v_defValue_1097_);
return v___x_1100_;
}
else
{
lean_object* v_val_1101_; 
v_val_1101_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_val_1101_);
lean_dec_ref_known(v___x_1099_, 1);
if (lean_obj_tag(v_val_1101_) == 1)
{
uint8_t v_v_1102_; 
v_v_1102_ = lean_ctor_get_uint8(v_val_1101_, 0);
lean_dec_ref_known(v_val_1101_, 0);
return v_v_1102_;
}
else
{
uint8_t v___x_1103_; 
lean_dec(v_val_1101_);
v___x_1103_ = lean_unbox(v_defValue_1097_);
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18___boxed(lean_object* v_opts_1104_, lean_object* v_opt_1105_){
_start:
{
uint8_t v_res_1106_; lean_object* v_r_1107_; 
v_res_1106_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(v_opts_1104_, v_opt_1105_);
lean_dec_ref(v_opt_1105_);
lean_dec_ref(v_opts_1104_);
v_r_1107_ = lean_box(v_res_1106_);
return v_r_1107_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_box(1);
v___x_1109_ = l_Lean_MessageData_ofFormat(v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2));
v___x_1114_ = l_Lean_MessageData_ofFormat(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
if (lean_obj_tag(v_x_1116_) == 0)
{
return v_x_1115_;
}
else
{
lean_object* v_head_1117_; lean_object* v_tail_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1140_; 
v_head_1117_ = lean_ctor_get(v_x_1116_, 0);
v_tail_1118_ = lean_ctor_get(v_x_1116_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_x_1116_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1120_ = v_x_1116_;
v_isShared_1121_ = v_isSharedCheck_1140_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_tail_1118_);
lean_inc(v_head_1117_);
lean_dec(v_x_1116_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1140_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_before_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1138_; 
v_before_1122_ = lean_ctor_get(v_head_1117_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_head_1117_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v_head_1117_, 1);
lean_dec(v_unused_1139_);
v___x_1124_ = v_head_1117_;
v_isShared_1125_ = v_isSharedCheck_1138_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_before_1122_);
lean_dec(v_head_1117_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1138_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1126_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 7);
lean_ctor_set(v___x_1124_, 1, v___x_1126_);
lean_ctor_set(v___x_1124_, 0, v_x_1115_);
v___x_1128_ = v___x_1124_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_x_1115_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 7);
lean_ctor_set(v___x_1120_, 1, v___x_1129_);
lean_ctor_set(v___x_1120_, 0, v___x_1128_);
v___x_1131_ = v___x_1120_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = l_Lean_MessageData_ofSyntax(v_before_1122_);
v___x_1133_ = l_Lean_indentD(v___x_1132_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1131_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v_x_1115_ = v___x_1134_;
v_x_1116_ = v_tail_1118_;
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
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1));
v___x_1145_ = l_Lean_MessageData_ofFormat(v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(lean_object* v_msgData_1146_, lean_object* v_macroStack_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_scopes_1152_; lean_object* v___x_1153_; lean_object* v_opts_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1150_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1151_ = lean_st_ref_get(v___y_1148_);
v_scopes_1152_ = lean_ctor_get(v___x_1151_, 2);
lean_inc(v_scopes_1152_);
lean_dec(v___x_1151_);
v___x_1153_ = l_List_head_x21___redArg(v___x_1150_, v_scopes_1152_);
lean_dec(v_scopes_1152_);
v_opts_1154_ = lean_ctor_get(v___x_1153_, 1);
lean_inc_ref(v_opts_1154_);
lean_dec(v___x_1153_);
v___x_1155_ = l_Lean_Elab_pp_macroStack;
v___x_1156_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(v_opts_1154_, v___x_1155_);
lean_dec_ref(v_opts_1154_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec(v_macroStack_1147_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_msgData_1146_);
return v___x_1157_;
}
else
{
if (lean_obj_tag(v_macroStack_1147_) == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_msgData_1146_);
return v___x_1158_;
}
else
{
lean_object* v_head_1159_; lean_object* v_after_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1175_; 
v_head_1159_ = lean_ctor_get(v_macroStack_1147_, 0);
lean_inc(v_head_1159_);
v_after_1160_ = lean_ctor_get(v_head_1159_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_head_1159_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v_head_1159_, 0);
lean_dec(v_unused_1176_);
v___x_1162_ = v_head_1159_;
v_isShared_1163_ = v_isSharedCheck_1175_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_after_1160_);
lean_dec(v_head_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1175_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0);
if (v_isShared_1163_ == 0)
{
lean_ctor_set_tag(v___x_1162_, 7);
lean_ctor_set(v___x_1162_, 1, v___x_1164_);
lean_ctor_set(v___x_1162_, 0, v_msgData_1146_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_msgData_1146_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v_msgData_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1167_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = l_Lean_MessageData_ofSyntax(v_after_1160_);
v___x_1170_ = l_Lean_indentD(v___x_1169_);
v_msgData_1171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1171_, 0, v___x_1168_);
lean_ctor_set(v_msgData_1171_, 1, v___x_1170_);
v___x_1172_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(v_msgData_1171_, v_macroStack_1147_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___boxed(lean_object* v_msgData_1177_, lean_object* v_macroStack_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_1177_, v_macroStack_1178_, v___y_1179_);
lean_dec(v___y_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(lean_object* v_msg_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Elab_Command_getRef___redArg(v___y_1183_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v_macroStack_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_a_1191_; lean_object* v___x_1192_; lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1201_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v_macroStack_1188_ = lean_ctor_get(v___y_1183_, 4);
v___x_1189_ = l_Lean_Elab_getBetterRef(v_a_1187_, v_macroStack_1188_);
lean_dec(v_a_1187_);
v___x_1190_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_1182_, v___y_1184_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref(v___x_1190_);
lean_inc(v_macroStack_1188_);
v___x_1192_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_a_1191_, v_macroStack_1188_, v___y_1184_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1189_);
lean_ctor_set(v___x_1197_, 1, v_a_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set_tag(v___x_1195_, 1);
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v_msg_1182_);
v_a_1202_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1186_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1186_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg___boxed(lean_object* v_msg_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(lean_object* v_ref_1215_, lean_object* v_msg_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_Elab_Command_getRef___redArg(v___y_1217_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v_fileName_1222_; lean_object* v_fileMap_1223_; lean_object* v_currRecDepth_1224_; lean_object* v_cmdPos_1225_; lean_object* v_macroStack_1226_; lean_object* v_quotContext_x3f_1227_; lean_object* v_currMacroScope_1228_; lean_object* v_snap_x3f_1229_; lean_object* v_cancelTk_x3f_1230_; uint8_t v_suppressElabErrors_1231_; lean_object* v_ref_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v_fileName_1222_ = lean_ctor_get(v___y_1217_, 0);
v_fileMap_1223_ = lean_ctor_get(v___y_1217_, 1);
v_currRecDepth_1224_ = lean_ctor_get(v___y_1217_, 2);
v_cmdPos_1225_ = lean_ctor_get(v___y_1217_, 3);
v_macroStack_1226_ = lean_ctor_get(v___y_1217_, 4);
v_quotContext_x3f_1227_ = lean_ctor_get(v___y_1217_, 5);
v_currMacroScope_1228_ = lean_ctor_get(v___y_1217_, 6);
v_snap_x3f_1229_ = lean_ctor_get(v___y_1217_, 8);
v_cancelTk_x3f_1230_ = lean_ctor_get(v___y_1217_, 9);
v_suppressElabErrors_1231_ = lean_ctor_get_uint8(v___y_1217_, sizeof(void*)*10);
v_ref_1232_ = l_Lean_replaceRef(v_ref_1215_, v_a_1221_);
lean_dec(v_a_1221_);
lean_inc(v_cancelTk_x3f_1230_);
lean_inc(v_snap_x3f_1229_);
lean_inc(v_currMacroScope_1228_);
lean_inc(v_quotContext_x3f_1227_);
lean_inc(v_macroStack_1226_);
lean_inc(v_cmdPos_1225_);
lean_inc(v_currRecDepth_1224_);
lean_inc_ref(v_fileMap_1223_);
lean_inc_ref(v_fileName_1222_);
v___x_1233_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1233_, 0, v_fileName_1222_);
lean_ctor_set(v___x_1233_, 1, v_fileMap_1223_);
lean_ctor_set(v___x_1233_, 2, v_currRecDepth_1224_);
lean_ctor_set(v___x_1233_, 3, v_cmdPos_1225_);
lean_ctor_set(v___x_1233_, 4, v_macroStack_1226_);
lean_ctor_set(v___x_1233_, 5, v_quotContext_x3f_1227_);
lean_ctor_set(v___x_1233_, 6, v_currMacroScope_1228_);
lean_ctor_set(v___x_1233_, 7, v_ref_1232_);
lean_ctor_set(v___x_1233_, 8, v_snap_x3f_1229_);
lean_ctor_set(v___x_1233_, 9, v_cancelTk_x3f_1230_);
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*10, v_suppressElabErrors_1231_);
v___x_1234_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1216_, v___x_1233_, v___y_1218_);
lean_dec_ref_known(v___x_1233_, 10);
return v___x_1234_;
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v_msg_1216_);
v_a_1235_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1220_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1220_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1243_, lean_object* v_msg_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_1243_, v_msg_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v_ref_1243_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(lean_object* v_env_1249_, lean_object* v_declName_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v___x_1253_; lean_object* v_env_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; uint8_t v___x_1257_; 
v___x_1253_ = 0;
v_env_1254_ = l_Lean_Environment_setExporting(v_env_1249_, v___x_1253_);
lean_inc(v_declName_1250_);
v___x_1255_ = l_Lean_mkPrivateName(v_env_1254_, v_declName_1250_);
v___x_1256_ = 1;
lean_inc_ref(v_env_1254_);
v___x_1257_ = l_Lean_Environment_contains(v_env_1254_, v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1258_ = l_Lean_privateToUserName(v_declName_1250_);
v___x_1259_ = l_Lean_Environment_contains(v_env_1254_, v___x_1258_, v___x_1256_);
v___x_1260_ = lean_box(v___x_1259_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set(v___x_1261_, 1, v___y_1252_);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec_ref(v_env_1254_);
lean_dec(v_declName_1250_);
v___x_1262_ = lean_box(v___x_1257_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___y_1252_);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed(lean_object* v_env_1264_, lean_object* v_declName_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(v_env_1264_, v_declName_1265_, v___y_1266_, v___y_1267_);
lean_dec_ref(v___y_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(lean_object* v_as_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
if (lean_obj_tag(v_as_1269_) == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
return v___x_1274_;
}
else
{
lean_object* v_head_1275_; lean_object* v_tail_1276_; lean_object* v_fst_1277_; lean_object* v_snd_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_scopes_1283_; lean_object* v___x_1284_; lean_object* v_opts_1285_; uint8_t v_hasTrace_1286_; 
v_head_1275_ = lean_ctor_get(v_as_1269_, 0);
lean_inc(v_head_1275_);
v_tail_1276_ = lean_ctor_get(v_as_1269_, 1);
lean_inc(v_tail_1276_);
lean_dec_ref_known(v_as_1269_, 2);
v_fst_1277_ = lean_ctor_get(v_head_1275_, 0);
lean_inc(v_fst_1277_);
v_snd_1278_ = lean_ctor_get(v_head_1275_, 1);
lean_inc(v_snd_1278_);
lean_dec(v_head_1275_);
v___x_1279_ = l_Lean_inheritedTraceOptions;
v___x_1280_ = lean_st_ref_get(v___x_1279_);
v___x_1281_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1282_ = lean_st_ref_get(v___y_1271_);
v_scopes_1283_ = lean_ctor_get(v___x_1282_, 2);
lean_inc(v_scopes_1283_);
lean_dec(v___x_1282_);
v___x_1284_ = l_List_head_x21___redArg(v___x_1281_, v_scopes_1283_);
lean_dec(v_scopes_1283_);
v_opts_1285_ = lean_ctor_get(v___x_1284_, 1);
lean_inc_ref(v_opts_1285_);
lean_dec(v___x_1284_);
v_hasTrace_1286_ = lean_ctor_get_uint8(v_opts_1285_, sizeof(void*)*1);
if (v_hasTrace_1286_ == 0)
{
lean_dec_ref(v_opts_1285_);
lean_dec(v___x_1280_);
lean_dec(v_snd_1278_);
lean_dec(v_fst_1277_);
v_as_1269_ = v_tail_1276_;
goto _start;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9));
lean_inc(v_fst_1277_);
v___x_1289_ = l_Lean_Name_append(v___x_1288_, v_fst_1277_);
v___x_1290_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1280_, v_opts_1285_, v___x_1289_);
lean_dec(v___x_1289_);
lean_dec_ref(v_opts_1285_);
lean_dec(v___x_1280_);
if (v___x_1290_ == 0)
{
lean_dec(v_snd_1278_);
lean_dec(v_fst_1277_);
v_as_1269_ = v_tail_1276_;
goto _start;
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1292_, 0, v_snd_1278_);
v___x_1293_ = l_Lean_MessageData_ofFormat(v___x_1292_);
v___x_1294_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_fst_1277_, v___x_1293_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_dec_ref_known(v___x_1294_, 1);
v_as_1269_ = v_tail_1276_;
goto _start;
}
else
{
lean_dec(v_tail_1276_);
return v___x_1294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3___boxed(lean_object* v_as_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v_as_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(lean_object* v_env_1301_, lean_object* v_opts_1302_, lean_object* v_currNamespace_1303_, lean_object* v_openDecls_1304_, lean_object* v_n_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = l_Lean_ResolveName_resolveGlobalName(v_env_1301_, v_opts_1302_, v_currNamespace_1303_, v_openDecls_1304_, v_n_1305_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___y_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed(lean_object* v_env_1310_, lean_object* v_opts_1311_, lean_object* v_currNamespace_1312_, lean_object* v_openDecls_1313_, lean_object* v_n_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(v_env_1310_, v_opts_1311_, v_currNamespace_1312_, v_openDecls_1313_, v_n_1314_, v___y_1315_, v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec_ref(v_opts_1311_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(lean_object* v_x_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; lean_object* v_env_1324_; lean_object* v___f_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v_scopes_1329_; lean_object* v___x_1330_; lean_object* v_opts_1331_; lean_object* v___x_1332_; 
v___x_1323_ = lean_st_ref_get(v___y_1321_);
v_env_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc_ref_n(v_env_1324_, 3);
lean_dec(v___x_1323_);
v___f_1325_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1325_, 0, v_env_1324_);
v___f_1326_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1326_, 0, v_env_1324_);
v___x_1327_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1328_ = lean_st_ref_get(v___y_1321_);
v_scopes_1329_ = lean_ctor_get(v___x_1328_, 2);
lean_inc(v_scopes_1329_);
lean_dec(v___x_1328_);
v___x_1330_ = l_List_head_x21___redArg(v___x_1327_, v_scopes_1329_);
lean_dec(v_scopes_1329_);
v_opts_1331_ = lean_ctor_get(v___x_1330_, 1);
lean_inc_ref(v_opts_1331_);
lean_dec(v___x_1330_);
v___x_1332_ = l_Lean_Elab_Command_getScope___redArg(v___y_1321_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v_currNamespace_1334_; lean_object* v___f_1335_; lean_object* v___x_1336_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v_currNamespace_1334_ = lean_ctor_get(v_a_1333_, 2);
lean_inc_n(v_currNamespace_1334_, 2);
lean_dec(v_a_1333_);
v___f_1335_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1335_, 0, v_currNamespace_1334_);
v___x_1336_ = l_Lean_Elab_Command_getScope___redArg(v___y_1321_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v_openDecls_1338_; lean_object* v___f_1339_; lean_object* v___f_1340_; lean_object* v_methods_1341_; lean_object* v___x_1342_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v_openDecls_1338_ = lean_ctor_get(v_a_1337_, 3);
lean_inc_n(v_openDecls_1338_, 2);
lean_dec(v_a_1337_);
lean_inc(v_currNamespace_1334_);
lean_inc_ref(v_env_1324_);
v___f_1339_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1339_, 0, v_env_1324_);
lean_closure_set(v___f_1339_, 1, v_currNamespace_1334_);
lean_closure_set(v___f_1339_, 2, v_openDecls_1338_);
v___f_1340_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1340_, 0, v_env_1324_);
lean_closure_set(v___f_1340_, 1, v_opts_1331_);
lean_closure_set(v___f_1340_, 2, v_currNamespace_1334_);
lean_closure_set(v___f_1340_, 3, v_openDecls_1338_);
v_methods_1341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1341_, 0, v___f_1326_);
lean_ctor_set(v_methods_1341_, 1, v___f_1335_);
lean_ctor_set(v_methods_1341_, 2, v___f_1325_);
lean_ctor_set(v_methods_1341_, 3, v___f_1339_);
lean_ctor_set(v_methods_1341_, 4, v___f_1340_);
v___x_1342_ = l_Lean_Elab_Command_getRef___redArg(v___y_1320_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1344_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1320_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v_currRecDepth_1346_; lean_object* v_quotContext_x3f_1347_; lean_object* v_a_1349_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v_currRecDepth_1346_ = lean_ctor_get(v___y_1320_, 2);
v_quotContext_x3f_1347_ = lean_ctor_get(v___y_1320_, 5);
if (lean_obj_tag(v_quotContext_x3f_1347_) == 0)
{
lean_object* v___x_1423_; lean_object* v_a_1424_; 
v___x_1423_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_1321_);
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref(v___x_1423_);
v_a_1349_ = v_a_1424_;
goto v___jp_1348_;
}
else
{
lean_object* v_val_1425_; 
v_val_1425_ = lean_ctor_get(v_quotContext_x3f_1347_, 0);
lean_inc(v_val_1425_);
v_a_1349_ = v_val_1425_;
goto v___jp_1348_;
}
v___jp_1348_:
{
lean_object* v___x_1350_; lean_object* v_maxRecDepth_1351_; lean_object* v___x_1352_; lean_object* v_nextMacroScope_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1350_ = lean_st_ref_get(v___y_1321_);
v_maxRecDepth_1351_ = lean_ctor_get(v___x_1350_, 5);
lean_inc(v_maxRecDepth_1351_);
lean_dec(v___x_1350_);
v___x_1352_ = lean_st_ref_get(v___y_1321_);
v_nextMacroScope_1353_ = lean_ctor_get(v___x_1352_, 4);
lean_inc(v_nextMacroScope_1353_);
lean_dec(v___x_1352_);
lean_inc(v_currRecDepth_1346_);
v___x_1354_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1354_, 0, v_methods_1341_);
lean_ctor_set(v___x_1354_, 1, v_a_1349_);
lean_ctor_set(v___x_1354_, 2, v_a_1345_);
lean_ctor_set(v___x_1354_, 3, v_currRecDepth_1346_);
lean_ctor_set(v___x_1354_, 4, v_maxRecDepth_1351_);
lean_ctor_set(v___x_1354_, 5, v_a_1343_);
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1356_, 0, v_nextMacroScope_1353_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
lean_ctor_set(v___x_1356_, 2, v___x_1355_);
v___x_1357_ = lean_apply_2(v_x_1319_, v___x_1354_, v___x_1356_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v_a_1359_; lean_object* v_macroScope_1360_; lean_object* v_traceMsgs_1361_; lean_object* v_expandedMacroDecls_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 1);
lean_inc(v_a_1358_);
v_a_1359_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1357_, 2);
v_macroScope_1360_ = lean_ctor_get(v_a_1358_, 0);
lean_inc(v_macroScope_1360_);
v_traceMsgs_1361_ = lean_ctor_get(v_a_1358_, 1);
lean_inc(v_traceMsgs_1361_);
v_expandedMacroDecls_1362_ = lean_ctor_get(v_a_1358_, 2);
lean_inc(v_expandedMacroDecls_1362_);
lean_dec(v_a_1358_);
v___x_1363_ = lean_box(0);
v___x_1364_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_expandedMacroDecls_1362_, v___x_1363_, v___y_1320_, v___y_1321_);
lean_dec(v_expandedMacroDecls_1362_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; lean_object* v_env_1366_; lean_object* v_messages_1367_; lean_object* v_scopes_1368_; lean_object* v_usedQuotCtxts_1369_; lean_object* v_maxRecDepth_1370_; lean_object* v_ngen_1371_; lean_object* v_auxDeclNGen_1372_; lean_object* v_infoState_1373_; lean_object* v_traceState_1374_; lean_object* v_snapshotTasks_1375_; lean_object* v_prevLinterStates_1376_; lean_object* v_codeQualityEntryTasks_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1403_; 
lean_dec_ref_known(v___x_1364_, 1);
v___x_1365_ = lean_st_ref_take(v___y_1321_);
v_env_1366_ = lean_ctor_get(v___x_1365_, 0);
v_messages_1367_ = lean_ctor_get(v___x_1365_, 1);
v_scopes_1368_ = lean_ctor_get(v___x_1365_, 2);
v_usedQuotCtxts_1369_ = lean_ctor_get(v___x_1365_, 3);
v_maxRecDepth_1370_ = lean_ctor_get(v___x_1365_, 5);
v_ngen_1371_ = lean_ctor_get(v___x_1365_, 6);
v_auxDeclNGen_1372_ = lean_ctor_get(v___x_1365_, 7);
v_infoState_1373_ = lean_ctor_get(v___x_1365_, 8);
v_traceState_1374_ = lean_ctor_get(v___x_1365_, 9);
v_snapshotTasks_1375_ = lean_ctor_get(v___x_1365_, 10);
v_prevLinterStates_1376_ = lean_ctor_get(v___x_1365_, 11);
v_codeQualityEntryTasks_1377_ = lean_ctor_get(v___x_1365_, 12);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v___x_1365_, 4);
lean_dec(v_unused_1404_);
v___x_1379_ = v___x_1365_;
v_isShared_1380_ = v_isSharedCheck_1403_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1377_);
lean_inc(v_prevLinterStates_1376_);
lean_inc(v_snapshotTasks_1375_);
lean_inc(v_traceState_1374_);
lean_inc(v_infoState_1373_);
lean_inc(v_auxDeclNGen_1372_);
lean_inc(v_ngen_1371_);
lean_inc(v_maxRecDepth_1370_);
lean_inc(v_usedQuotCtxts_1369_);
lean_inc(v_scopes_1368_);
lean_inc(v_messages_1367_);
lean_inc(v_env_1366_);
lean_dec(v___x_1365_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1403_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 4, v_macroScope_1360_);
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_env_1366_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_messages_1367_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_scopes_1368_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_usedQuotCtxts_1369_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v_macroScope_1360_);
lean_ctor_set(v_reuseFailAlloc_1402_, 5, v_maxRecDepth_1370_);
lean_ctor_set(v_reuseFailAlloc_1402_, 6, v_ngen_1371_);
lean_ctor_set(v_reuseFailAlloc_1402_, 7, v_auxDeclNGen_1372_);
lean_ctor_set(v_reuseFailAlloc_1402_, 8, v_infoState_1373_);
lean_ctor_set(v_reuseFailAlloc_1402_, 9, v_traceState_1374_);
lean_ctor_set(v_reuseFailAlloc_1402_, 10, v_snapshotTasks_1375_);
lean_ctor_set(v_reuseFailAlloc_1402_, 11, v_prevLinterStates_1376_);
lean_ctor_set(v_reuseFailAlloc_1402_, 12, v_codeQualityEntryTasks_1377_);
v___x_1382_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = lean_st_ref_put(v___y_1321_, v___x_1382_);
v___x_1384_ = l_List_reverse___redArg(v_traceMsgs_1361_);
v___x_1385_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v___x_1384_, v___y_1320_, v___y_1321_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1385_, 0);
lean_dec(v_unused_1393_);
v___x_1387_ = v___x_1385_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v___x_1385_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v_a_1359_);
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1359_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_a_1359_);
v_a_1394_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1385_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1385_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_traceMsgs_1361_);
lean_dec(v_macroScope_1360_);
lean_dec(v_a_1359_);
v_a_1405_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1364_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1364_);
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
else
{
lean_object* v_a_1413_; 
v_a_1413_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1357_, 2);
if (lean_obj_tag(v_a_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v_a_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v_a_1414_ = lean_ctor_get(v_a_1413_, 0);
lean_inc(v_a_1414_);
v_a_1415_ = lean_ctor_get(v_a_1413_, 1);
lean_inc_ref(v_a_1415_);
lean_dec_ref_known(v_a_1413_, 2);
v___x_1416_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0));
v___x_1417_ = lean_string_dec_eq(v_a_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_a_1415_);
v___x_1419_ = l_Lean_MessageData_ofFormat(v___x_1418_);
v___x_1420_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_a_1414_, v___x_1419_, v___y_1320_, v___y_1321_);
lean_dec(v_a_1414_);
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; 
lean_dec_ref(v_a_1415_);
v___x_1421_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_a_1414_);
return v___x_1421_;
}
}
else
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v___x_1422_;
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_a_1343_);
lean_dec_ref_known(v_methods_1341_, 5);
lean_dec_ref(v_x_1319_);
v_a_1426_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1344_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1344_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec_ref_known(v_methods_1341_, 5);
lean_dec_ref(v_x_1319_);
v_a_1434_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1342_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1342_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec_ref(v___f_1335_);
lean_dec(v_currNamespace_1334_);
lean_dec_ref(v_opts_1331_);
lean_dec_ref(v___f_1326_);
lean_dec_ref(v___f_1325_);
lean_dec_ref(v_env_1324_);
lean_dec_ref(v_x_1319_);
v_a_1442_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1336_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1336_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v_opts_1331_);
lean_dec_ref(v___f_1326_);
lean_dec_ref(v___f_1325_);
lean_dec_ref(v_env_1324_);
lean_dec_ref(v_x_1319_);
v_a_1450_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1332_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1332_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___boxed(lean_object* v_x_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v_x_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1462_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1478_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9));
v___x_1479_ = l_Lean_Name_append(v___x_1478_, v___x_1477_);
return v___x_1479_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__8));
v___x_1482_ = l_Lean_stringToMessageData(v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__10));
v___x_1485_ = l_Lean_stringToMessageData(v___x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object* v_modifiers_1486_, lean_object* v_stx_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v___x_1491_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v_declId_1498_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1511_ = l_Lean_Syntax_getArg(v_stx_1487_, v___x_1491_);
v___x_1512_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_1512_, 0, v___x_1511_);
v___x_1513_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_1512_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = lean_unsigned_to_nat(2u);
v___x_1538_ = l_Lean_Syntax_getArg(v_stx_1487_, v___x_1515_);
v___x_1539_ = lean_alloc_closure((void*)(l_Lean_Elab_expandOptNamedPrio___boxed), 3, 1);
lean_closure_set(v___x_1539_, 0, v___x_1538_);
v___x_1540_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_1539_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1542_ = l_Lean_Elab_Command_getRef___redArg(v_a_1488_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1680_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = 0;
v___x_1545_ = l_Lean_SourceInfo_fromRef(v_a_1543_, v___x_1544_);
lean_dec(v_a_1543_);
v___x_1680_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1488_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_quotContext_x3f_1681_; 
lean_dec_ref_known(v___x_1680_, 1);
v_quotContext_x3f_1681_ = lean_ctor_get(v_a_1488_, 5);
if (lean_obj_tag(v_quotContext_x3f_1681_) == 0)
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1489_);
lean_dec_ref(v___x_1682_);
goto v___jp_1546_;
}
else
{
goto v___jp_1546_;
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec(v___x_1545_);
lean_dec(v_a_1541_);
lean_dec(v_a_1514_);
lean_dec(v_stx_1487_);
lean_dec_ref(v_modifiers_1486_);
v_a_1683_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1680_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1680_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
v___jp_1546_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v_fst_1554_; lean_object* v_snd_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1679_; 
v___x_1547_ = ((lean_object*)(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_21_));
v___x_1548_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2));
v___x_1549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0));
v___x_1550_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4));
v___x_1551_ = lean_unsigned_to_nat(4u);
v___x_1552_ = l_Lean_Syntax_getArg(v_stx_1487_, v___x_1551_);
v___x_1553_ = l_Lean_Elab_expandDeclSig(v___x_1552_);
lean_dec(v___x_1552_);
v_fst_1554_ = lean_ctor_get(v___x_1553_, 0);
v_snd_1555_ = lean_ctor_get(v___x_1553_, 1);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1557_ = v___x_1553_;
v_isShared_1558_ = v_isSharedCheck_1679_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_snd_1555_);
lean_inc(v_fst_1554_);
lean_dec(v___x_1553_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1679_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
lean_inc(v___x_1545_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set_tag(v___x_1557_, 2);
lean_ctor_set(v___x_1557_, 1, v___x_1549_);
lean_ctor_set(v___x_1557_, 0, v___x_1545_);
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1549_);
v___x_1560_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1561_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1562_ = l_Nat_reprFast(v_a_1541_);
v___x_1563_ = lean_box(2);
v___x_1564_ = l_Lean_Syntax_mkNumLit(v___x_1562_, v___x_1563_);
lean_inc(v___x_1545_);
v___x_1565_ = l_Lean_Syntax_node1(v___x_1545_, v___x_1561_, v___x_1564_);
v___x_1566_ = l_Lean_Syntax_node2(v___x_1545_, v___x_1550_, v___x_1560_, v___x_1565_);
v___x_1567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1));
v___x_1568_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v___x_1566_);
v___x_1569_ = lean_unbox(v_a_1514_);
lean_dec(v_a_1514_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*2, v___x_1569_);
v___x_1570_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_1486_, v___x_1568_);
v___x_1571_ = lean_unsigned_to_nat(3u);
v___x_1572_ = l_Lean_Syntax_getArg(v_stx_1487_, v___x_1571_);
v___x_1573_ = l_Lean_Syntax_getOptional_x3f(v___x_1572_);
lean_dec(v___x_1572_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = l_Lean_Syntax_getArgs(v_fst_1554_);
lean_inc(v_snd_1555_);
v___x_1575_ = l_Lean_Elab_Command_mkInstanceName(v___x_1574_, v_snd_1555_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_scopes_1582_; lean_object* v___x_1583_; lean_object* v_opts_1584_; uint8_t v_hasTrace_1585_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v___x_1577_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1578_ = l_Lean_inheritedTraceOptions;
v___x_1579_ = lean_st_ref_get(v___x_1578_);
v___x_1580_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1581_ = lean_st_ref_get(v_a_1489_);
v_scopes_1582_ = lean_ctor_get(v___x_1581_, 2);
lean_inc(v_scopes_1582_);
lean_dec(v___x_1581_);
v___x_1583_ = l_List_head_x21___redArg(v___x_1580_, v_scopes_1582_);
lean_dec(v_scopes_1582_);
v_opts_1584_ = lean_ctor_get(v___x_1583_, 1);
lean_inc_ref(v_opts_1584_);
lean_dec(v___x_1583_);
v_hasTrace_1585_ = lean_ctor_get_uint8(v_opts_1584_, sizeof(void*)*1);
if (v_hasTrace_1585_ == 0)
{
lean_dec_ref(v_opts_1584_);
lean_dec(v___x_1579_);
v___y_1517_ = v___x_1548_;
v___y_1518_ = v_fst_1554_;
v___y_1519_ = v_a_1576_;
v___y_1520_ = v___x_1561_;
v___y_1521_ = v___x_1563_;
v___y_1522_ = v___x_1570_;
v___y_1523_ = v___x_1547_;
v___y_1524_ = v_snd_1555_;
goto v___jp_1516_;
}
else
{
lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__7, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7);
v___x_1587_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1579_, v_opts_1584_, v___x_1586_);
lean_dec_ref(v_opts_1584_);
lean_dec(v___x_1579_);
if (v___x_1587_ == 0)
{
v___y_1517_ = v___x_1548_;
v___y_1518_ = v_fst_1554_;
v___y_1519_ = v_a_1576_;
v___y_1520_ = v___x_1561_;
v___y_1521_ = v___x_1563_;
v___y_1522_ = v___x_1570_;
v___y_1523_ = v___x_1547_;
v___y_1524_ = v_snd_1555_;
goto v___jp_1516_;
}
else
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_Elab_Command_getScope___redArg(v_a_1489_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v_currNamespace_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1588_, 1);
v_currNamespace_1590_ = lean_ctor_get(v_a_1589_, 2);
lean_inc(v_currNamespace_1590_);
lean_dec(v_a_1589_);
v___x_1591_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__9, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
lean_inc(v_a_1576_);
v___x_1592_ = l_Lean_Name_append(v_currNamespace_1590_, v_a_1576_);
v___x_1593_ = l_Lean_MessageData_ofName(v___x_1592_);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1591_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_1577_, v___x_1594_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_dec_ref_known(v___x_1595_, 1);
v___y_1517_ = v___x_1548_;
v___y_1518_ = v_fst_1554_;
v___y_1519_ = v_a_1576_;
v___y_1520_ = v___x_1561_;
v___y_1521_ = v___x_1563_;
v___y_1522_ = v___x_1570_;
v___y_1523_ = v___x_1547_;
v___y_1524_ = v_snd_1555_;
goto v___jp_1516_;
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_a_1576_);
lean_dec_ref(v___x_1570_);
lean_dec(v_snd_1555_);
lean_dec(v_fst_1554_);
lean_dec(v_stx_1487_);
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_a_1576_);
lean_dec_ref(v___x_1570_);
lean_dec(v_snd_1555_);
lean_dec(v_fst_1554_);
lean_dec(v_stx_1487_);
v_a_1604_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1588_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1588_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v___x_1570_);
lean_dec(v_snd_1555_);
lean_dec(v_fst_1554_);
lean_dec(v_stx_1487_);
v_a_1612_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1575_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1575_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v_val_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v_scopes_1626_; lean_object* v___x_1627_; lean_object* v_opts_1628_; uint8_t v_hasTrace_1629_; 
v_val_1620_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_val_1620_);
lean_dec_ref_known(v___x_1573_, 1);
v___x_1621_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_1622_ = l_Lean_inheritedTraceOptions;
v___x_1623_ = lean_st_ref_get(v___x_1622_);
v___x_1624_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1625_ = lean_st_ref_get(v_a_1489_);
v_scopes_1626_ = lean_ctor_get(v___x_1625_, 2);
lean_inc(v_scopes_1626_);
lean_dec(v___x_1625_);
v___x_1627_ = l_List_head_x21___redArg(v___x_1624_, v_scopes_1626_);
lean_dec(v_scopes_1626_);
v_opts_1628_ = lean_ctor_get(v___x_1627_, 1);
lean_inc_ref(v_opts_1628_);
lean_dec(v___x_1627_);
v_hasTrace_1629_ = lean_ctor_get_uint8(v_opts_1628_, sizeof(void*)*1);
if (v_hasTrace_1629_ == 0)
{
lean_dec_ref(v_opts_1628_);
lean_dec(v___x_1623_);
v___y_1493_ = v_fst_1554_;
v___y_1494_ = v___x_1561_;
v___y_1495_ = v___x_1563_;
v___y_1496_ = v___x_1570_;
v___y_1497_ = v_snd_1555_;
v_declId_1498_ = v_val_1620_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__7, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7);
v___x_1631_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1623_, v_opts_1628_, v___x_1630_);
lean_dec_ref(v_opts_1628_);
lean_dec(v___x_1623_);
if (v___x_1631_ == 0)
{
v___y_1493_ = v_fst_1554_;
v___y_1494_ = v___x_1561_;
v___y_1495_ = v___x_1563_;
v___y_1496_ = v___x_1570_;
v___y_1497_ = v_snd_1555_;
v_declId_1498_ = v_val_1620_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = l_Lean_Syntax_getArgs(v_fst_1554_);
lean_inc(v_snd_1555_);
v___x_1633_ = l_Lean_Elab_Command_mkInstanceName(v___x_1632_, v_snd_1555_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_scopes_1637_; lean_object* v___x_1638_; lean_object* v_opts_1639_; uint8_t v_hasTrace_1640_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = lean_st_ref_get(v___x_1622_);
v___x_1636_ = lean_st_ref_get(v_a_1489_);
v_scopes_1637_ = lean_ctor_get(v___x_1636_, 2);
lean_inc(v_scopes_1637_);
lean_dec(v___x_1636_);
v___x_1638_ = l_List_head_x21___redArg(v___x_1624_, v_scopes_1637_);
lean_dec(v_scopes_1637_);
v_opts_1639_ = lean_ctor_get(v___x_1638_, 1);
lean_inc_ref(v_opts_1639_);
lean_dec(v___x_1638_);
v_hasTrace_1640_ = lean_ctor_get_uint8(v_opts_1639_, sizeof(void*)*1);
if (v_hasTrace_1640_ == 0)
{
lean_dec_ref(v_opts_1639_);
lean_dec(v___x_1635_);
lean_dec(v_a_1634_);
v___y_1493_ = v_fst_1554_;
v___y_1494_ = v___x_1561_;
v___y_1495_ = v___x_1563_;
v___y_1496_ = v___x_1570_;
v___y_1497_ = v_snd_1555_;
v_declId_1498_ = v_val_1620_;
goto v___jp_1492_;
}
else
{
uint8_t v___x_1641_; 
v___x_1641_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1635_, v_opts_1639_, v___x_1630_);
lean_dec_ref(v_opts_1639_);
lean_dec(v___x_1635_);
if (v___x_1641_ == 0)
{
lean_dec(v_a_1634_);
v___y_1493_ = v_fst_1554_;
v___y_1494_ = v___x_1561_;
v___y_1495_ = v___x_1563_;
v___y_1496_ = v___x_1570_;
v___y_1497_ = v_snd_1555_;
v_declId_1498_ = v_val_1620_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Elab_Command_getScope___redArg(v_a_1489_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v_currNamespace_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1642_, 1);
v_currNamespace_1644_ = lean_ctor_get(v_a_1643_, 2);
lean_inc(v_currNamespace_1644_);
lean_dec(v_a_1643_);
v___x_1645_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__9, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
v___x_1646_ = l_Lean_Name_append(v_currNamespace_1644_, v_a_1634_);
v___x_1647_ = l_Lean_MessageData_ofName(v___x_1646_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1645_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfInstance___closed__11, &l_Lean_Elab_Command_mkDefViewOfInstance___closed__11_once, _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
lean_inc(v_val_1620_);
v___x_1651_ = l_Lean_MessageData_ofSyntax(v_val_1620_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_1621_, v___x_1652_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_dec_ref_known(v___x_1653_, 1);
v___y_1493_ = v_fst_1554_;
v___y_1494_ = v___x_1561_;
v___y_1495_ = v___x_1563_;
v___y_1496_ = v___x_1570_;
v___y_1497_ = v_snd_1555_;
v_declId_1498_ = v_val_1620_;
goto v___jp_1492_;
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v_val_1620_);
lean_dec_ref(v___x_1570_);
lean_dec(v_snd_1555_);
lean_dec(v_fst_1554_);
lean_dec(v_stx_1487_);
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
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
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_a_1634_);
lean_dec(v_val_1620_);
lean_dec_ref(v___x_1570_);
lean_dec(v_snd_1555_);
lean_dec(v_fst_1554_);
lean_dec(v_stx_1487_);
v_a_1662_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1642_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1642_);
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
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_val_1620_);
lean_dec_ref(v___x_1570_);
lean_dec(v_snd_1555_);
lean_dec(v_fst_1554_);
lean_dec(v_stx_1487_);
v_a_1670_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1633_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1633_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
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
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_a_1541_);
lean_dec(v_a_1514_);
lean_dec(v_stx_1487_);
lean_dec_ref(v_modifiers_1486_);
v_a_1691_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1542_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1542_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_a_1514_);
lean_dec(v_stx_1487_);
lean_dec_ref(v_modifiers_1486_);
v_a_1699_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1540_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1540_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
v___jp_1516_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1525_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0));
v___x_1526_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__1));
lean_inc_ref(v___y_1517_);
lean_inc_ref(v___y_1523_);
v___x_1527_ = l_Lean_Name_mkStr4(v___y_1523_, v___y_1517_, v___x_1525_, v___x_1526_);
v___x_1528_ = lean_unsigned_to_nat(1u);
v___x_1529_ = l_Lean_Syntax_getArg(v_stx_1487_, v___x_1528_);
v___x_1530_ = 1;
v___x_1531_ = l_Lean_mkIdentFrom(v___x_1529_, v___y_1519_, v___x_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = ((lean_object*)(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0));
lean_inc(v___y_1520_);
lean_inc_n(v___y_1521_, 2);
v___x_1533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1533_, 0, v___y_1521_);
lean_ctor_set(v___x_1533_, 1, v___y_1520_);
lean_ctor_set(v___x_1533_, 2, v___x_1532_);
v___x_1534_ = lean_mk_empty_array_with_capacity(v___x_1515_);
v___x_1535_ = lean_array_push(v___x_1534_, v___x_1531_);
v___x_1536_ = lean_array_push(v___x_1535_, v___x_1533_);
v___x_1537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1537_, 0, v___y_1521_);
lean_ctor_set(v___x_1537_, 1, v___x_1527_);
lean_ctor_set(v___x_1537_, 2, v___x_1536_);
v___y_1493_ = v___y_1518_;
v___y_1494_ = v___y_1520_;
v___y_1495_ = v___y_1521_;
v___y_1496_ = v___y_1522_;
v___y_1497_ = v___y_1524_;
v_declId_1498_ = v___x_1537_;
goto v___jp_1492_;
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_stx_1487_);
lean_dec_ref(v_modifiers_1486_);
v_a_1707_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1513_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1513_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
v___jp_1492_:
{
lean_object* v_docString_x3f_1499_; uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_docString_x3f_1499_ = lean_ctor_get(v___y_1496_, 1);
lean_inc(v_docString_x3f_1499_);
v___x_1500_ = 1;
v___x_1501_ = l_Lean_Syntax_getArgs(v_stx_1487_);
v___x_1502_ = lean_unsigned_to_nat(5u);
v___x_1503_ = l_Array_toSubarray___redArg(v___x_1501_, v___x_1491_, v___x_1502_);
v___x_1504_ = l_Subarray_copy___redArg(v___x_1503_);
v___x_1505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1505_, 0, v___y_1495_);
lean_ctor_set(v___x_1505_, 1, v___y_1494_);
lean_ctor_set(v___x_1505_, 2, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___y_1497_);
v___x_1507_ = l_Lean_Syntax_getArg(v_stx_1487_, v___x_1502_);
v___x_1508_ = lean_box(0);
v___x_1509_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1509_, 0, v_stx_1487_);
lean_ctor_set(v___x_1509_, 1, v___x_1505_);
lean_ctor_set(v___x_1509_, 2, v___y_1496_);
lean_ctor_set(v___x_1509_, 3, v_declId_1498_);
lean_ctor_set(v___x_1509_, 4, v___y_1493_);
lean_ctor_set(v___x_1509_, 5, v___x_1506_);
lean_ctor_set(v___x_1509_, 6, v___x_1507_);
lean_ctor_set(v___x_1509_, 7, v_docString_x3f_1499_);
lean_ctor_set(v___x_1509_, 8, v___x_1508_);
lean_ctor_set(v___x_1509_, 9, v___x_1508_);
lean_ctor_set_uint8(v___x_1509_, sizeof(void*)*10, v___x_1500_);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object* v_modifiers_1715_, lean_object* v_stx_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Elab_Command_mkDefViewOfInstance(v_modifiers_1715_, v_stx_1716_, v_a_1717_, v_a_1718_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(lean_object* v_00_u03b1_1721_, lean_object* v_x_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_1722_, v___y_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1726_, lean_object* v_x_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(v_00_u03b1_1726_, v_x_1727_, v___y_1728_, v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec_ref(v_x_1727_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(lean_object* v_00_u03b1_1731_, lean_object* v_ref_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_1732_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1737_, lean_object* v_ref_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(v_00_u03b1_1737_, v_ref_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(lean_object* v_00_u03b1_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(v_00_u03b1_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(lean_object* v_00_u03b1_1753_, lean_object* v_x_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v_x_1754_, v___y_1755_, v___y_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___boxed(lean_object* v_00_u03b1_1759_, lean_object* v_x_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(v_00_u03b1_1759_, v_x_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(lean_object* v_msgData_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_1765_, v___y_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___boxed(lean_object* v_msgData_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(v_msgData_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(lean_object* v_as_1775_, lean_object* v_as_x27_1776_, lean_object* v_b_1777_, lean_object* v_a_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_1776_, v_b_1777_, v___y_1779_, v___y_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___boxed(lean_object* v_as_1783_, lean_object* v_as_x27_1784_, lean_object* v_b_1785_, lean_object* v_a_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(v_as_1783_, v_as_x27_1784_, v_b_1785_, v_a_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v_as_x27_1784_);
lean_dec(v_as_1783_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(lean_object* v_00_u03b1_1791_, lean_object* v_ref_1792_, lean_object* v_msg_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_1792_, v_msg_1793_, v___y_1794_, v___y_1795_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1798_, lean_object* v_ref_1799_, lean_object* v_msg_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(v_00_u03b1_1798_, v_ref_1799_, v_msg_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v_ref_1799_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1805_, lean_object* v_m_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_1806_, v_a_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_1809_, lean_object* v_m_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(v_00_u03b2_1809_, v_m_1810_, v_a_1811_);
lean_dec(v_a_1811_);
lean_dec_ref(v_m_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(lean_object* v_00_u03b1_1813_, lean_object* v_msg_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_1814_, v___y_1815_, v___y_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_msg_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(v_00_u03b1_1819_, v_msg_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
return v_res_1824_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
uint8_t v___x_1828_; 
v___x_1828_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_1826_, v_x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1829_, lean_object* v_x_1830_, lean_object* v_x_1831_){
_start:
{
uint8_t v_res_1832_; lean_object* v_r_1833_; 
v_res_1832_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_1829_, v_x_1830_, v_x_1831_);
lean_dec_ref(v_x_1831_);
lean_dec_ref(v_x_1830_);
v_r_1833_ = lean_box(v_res_1832_);
return v_r_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1834_, lean_object* v_a_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_1835_, v_x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1838_, lean_object* v_a_1839_, lean_object* v_x_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(v_00_u03b2_1838_, v_a_1839_, v_x_1840_);
lean_dec(v_x_1840_);
lean_dec(v_a_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(lean_object* v_msgData_1842_, lean_object* v_macroStack_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_1842_, v_macroStack_1843_, v___y_1845_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___boxed(lean_object* v_msgData_1848_, lean_object* v_macroStack_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(v_msgData_1848_, v_macroStack_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1853_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_1854_, lean_object* v_x_1855_, size_t v_x_1856_, lean_object* v_x_1857_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_1855_, v_x_1856_, v_x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_){
_start:
{
size_t v_x_18433__boxed_1863_; uint8_t v_res_1864_; lean_object* v_r_1865_; 
v_x_18433__boxed_1863_ = lean_unbox_usize(v_x_1861_);
lean_dec(v_x_1861_);
v_res_1864_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_1859_, v_x_1860_, v_x_18433__boxed_1863_, v_x_1862_);
lean_dec_ref(v_x_1862_);
lean_dec_ref(v_x_1860_);
v_r_1865_ = lean_box(v_res_1864_);
return v_r_1865_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(lean_object* v_00_u03b2_1866_, lean_object* v_keys_1867_, lean_object* v_vals_1868_, lean_object* v_heq_1869_, lean_object* v_i_1870_, lean_object* v_k_1871_){
_start:
{
uint8_t v___x_1872_; 
v___x_1872_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_1867_, v_i_1870_, v_k_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___boxed(lean_object* v_00_u03b2_1873_, lean_object* v_keys_1874_, lean_object* v_vals_1875_, lean_object* v_heq_1876_, lean_object* v_i_1877_, lean_object* v_k_1878_){
_start:
{
uint8_t v_res_1879_; lean_object* v_r_1880_; 
v_res_1879_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(v_00_u03b2_1873_, v_keys_1874_, v_vals_1875_, v_heq_1876_, v_i_1877_, v_k_1878_);
lean_dec_ref(v_k_1878_);
lean_dec_ref(v_vals_1875_);
lean_dec_ref(v_keys_1874_);
v_r_1880_ = lean_box(v_res_1879_);
return v_r_1880_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6(void){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Array_mkArray0___redArg();
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque(lean_object* v_modifiers_1905_, lean_object* v_stx_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v_fst_1913_; lean_object* v_snd_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_2044_; 
v___x_1910_ = lean_unsigned_to_nat(2u);
v___x_1911_ = l_Lean_Syntax_getArg(v_stx_1906_, v___x_1910_);
v___x_1912_ = l_Lean_Elab_expandDeclSig(v___x_1911_);
lean_dec(v___x_1911_);
v_fst_1913_ = lean_ctor_get(v___x_1912_, 0);
v_snd_1914_ = lean_ctor_get(v___x_1912_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_1916_ = v___x_1912_;
v_isShared_1917_ = v_isSharedCheck_2044_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_snd_1914_);
lean_inc(v_fst_1913_);
lean_dec(v___x_1912_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_2044_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v_val_1919_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v_val_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = lean_unsigned_to_nat(3u);
v___x_1978_ = l_Lean_Syntax_getArg(v_stx_1906_, v___x_1977_);
v___x_1979_ = l_Lean_Syntax_getOptional_x3f(v___x_1978_);
lean_dec(v___x_1978_);
if (lean_obj_tag(v___x_1979_) == 0)
{
uint8_t v_isUnsafe_1980_; 
v_isUnsafe_1980_ = lean_ctor_get_uint8(v_modifiers_1905_, sizeof(void*)*3 + 4);
if (v_isUnsafe_1980_ == 0)
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_Elab_Command_getRef___redArg(v_a_1907_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1983_; lean_object* v___x_1992_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = l_Lean_SourceInfo_fromRef(v_a_1982_, v_isUnsafe_1980_);
lean_dec(v_a_1982_);
v___x_1992_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1907_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_quotContext_x3f_1993_; 
lean_dec_ref_known(v___x_1992_, 1);
v_quotContext_x3f_1993_ = lean_ctor_get(v_a_1907_, 5);
if (lean_obj_tag(v_quotContext_x3f_1993_) == 0)
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1908_);
lean_dec_ref(v___x_1994_);
goto v___jp_1984_;
}
else
{
goto v___jp_1984_;
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec(v___x_1983_);
lean_del_object(v___x_1916_);
lean_dec(v_snd_1914_);
lean_dec(v_fst_1913_);
lean_dec(v_stx_1906_);
lean_dec_ref(v_modifiers_1905_);
v_a_1995_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1992_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1992_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
v___jp_1984_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1985_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9));
v___x_1986_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10));
lean_inc_n(v___x_1983_, 2);
v___x_1987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1983_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1989_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6, &l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once, _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6);
v___x_1990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1983_);
lean_ctor_set(v___x_1990_, 1, v___x_1988_);
lean_ctor_set(v___x_1990_, 2, v___x_1989_);
v___x_1991_ = l_Lean_Syntax_node2(v___x_1983_, v___x_1985_, v___x_1987_, v___x_1990_);
v_val_1951_ = v___x_1991_;
v___y_1952_ = v_a_1907_;
v___y_1953_ = v_a_1908_;
goto v___jp_1950_;
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_del_object(v___x_1916_);
lean_dec(v_snd_1914_);
lean_dec(v_fst_1913_);
lean_dec(v_stx_1906_);
lean_dec_ref(v_modifiers_1905_);
v_a_2003_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1981_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1981_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_Elab_Command_getRef___redArg(v_a_1907_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2024_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2013_ = 0;
v___x_2014_ = l_Lean_SourceInfo_fromRef(v_a_2012_, v___x_2013_);
lean_dec(v_a_2012_);
v___x_2024_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_1907_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_quotContext_x3f_2025_; 
lean_dec_ref_known(v___x_2024_, 1);
v_quotContext_x3f_2025_ = lean_ctor_get(v_a_1907_, 5);
if (lean_obj_tag(v_quotContext_x3f_2025_) == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_1908_);
lean_dec_ref(v___x_2026_);
goto v___jp_2015_;
}
else
{
goto v___jp_2015_;
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v___x_2014_);
lean_del_object(v___x_1916_);
lean_dec(v_snd_1914_);
lean_dec(v_fst_1913_);
lean_dec(v_stx_1906_);
lean_dec_ref(v_modifiers_1905_);
v_a_2027_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2024_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2024_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
v___jp_2015_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2016_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9));
v___x_2017_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10));
lean_inc_n(v___x_2014_, 3);
v___x_2018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2014_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
v___x_2019_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_2020_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11));
v___x_2021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2014_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = l_Lean_Syntax_node1(v___x_2014_, v___x_2019_, v___x_2021_);
v___x_2023_ = l_Lean_Syntax_node2(v___x_2014_, v___x_2016_, v___x_2018_, v___x_2022_);
v_val_1951_ = v___x_2023_;
v___y_1952_ = v_a_1907_;
v___y_1953_ = v_a_1908_;
goto v___jp_1950_;
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_del_object(v___x_1916_);
lean_dec(v_snd_1914_);
lean_dec(v_fst_1913_);
lean_dec(v_stx_1906_);
lean_dec_ref(v_modifiers_1905_);
v_a_2035_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2011_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2011_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
else
{
lean_object* v_val_2043_; 
lean_del_object(v___x_1916_);
v_val_2043_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_val_2043_);
lean_dec_ref_known(v___x_1979_, 1);
v_val_1919_ = v_val_2043_;
goto v___jp_1918_;
}
v___jp_1918_:
{
lean_object* v_docString_x3f_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_docString_x3f_1920_ = lean_ctor_get(v_modifiers_1905_, 1);
lean_inc(v_docString_x3f_1920_);
v___x_1921_ = 4;
v___x_1922_ = l_Lean_Syntax_getArgs(v_stx_1906_);
v___x_1923_ = lean_unsigned_to_nat(3u);
v___x_1924_ = lean_unsigned_to_nat(0u);
v___x_1925_ = l_Array_toSubarray___redArg(v___x_1922_, v___x_1924_, v___x_1923_);
v___x_1926_ = l_Subarray_copy___redArg(v___x_1925_);
v___x_1927_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1928_ = lean_box(2);
v___x_1929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v___x_1927_);
lean_ctor_set(v___x_1929_, 2, v___x_1926_);
v___x_1930_ = lean_unsigned_to_nat(1u);
v___x_1931_ = l_Lean_Syntax_getArg(v_stx_1906_, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1932_, 0, v_snd_1914_);
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1934_, 0, v_stx_1906_);
lean_ctor_set(v___x_1934_, 1, v___x_1929_);
lean_ctor_set(v___x_1934_, 2, v_modifiers_1905_);
lean_ctor_set(v___x_1934_, 3, v___x_1931_);
lean_ctor_set(v___x_1934_, 4, v_fst_1913_);
lean_ctor_set(v___x_1934_, 5, v___x_1932_);
lean_ctor_set(v___x_1934_, 6, v_val_1919_);
lean_ctor_set(v___x_1934_, 7, v_docString_x3f_1920_);
lean_ctor_set(v___x_1934_, 8, v___x_1933_);
lean_ctor_set(v___x_1934_, 9, v___x_1933_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*10, v___x_1921_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
v___jp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1939_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1));
v___x_1940_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2));
lean_inc(v___y_1938_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 2);
lean_ctor_set(v___x_1916_, 1, v___x_1940_);
lean_ctor_set(v___x_1916_, 0, v___y_1938_);
v___x_1942_ = v___x_1916_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___y_1938_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1943_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5));
v___x_1944_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_1945_ = lean_obj_once(&l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6, &l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once, _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6);
lean_inc_n(v___y_1938_, 2);
v___x_1946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1946_, 0, v___y_1938_);
lean_ctor_set(v___x_1946_, 1, v___x_1944_);
lean_ctor_set(v___x_1946_, 2, v___x_1945_);
lean_inc_ref_n(v___x_1946_, 2);
v___x_1947_ = l_Lean_Syntax_node2(v___y_1938_, v___x_1943_, v___x_1946_, v___x_1946_);
v___x_1948_ = l_Lean_Syntax_node4(v___y_1938_, v___x_1939_, v___x_1942_, v___y_1937_, v___x_1947_, v___x_1946_);
v_val_1919_ = v___x_1948_;
goto v___jp_1918_;
}
}
v___jp_1950_:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_Elab_Command_getRef___redArg(v___y_1952_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; uint8_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = 0;
v___x_1957_ = l_Lean_SourceInfo_fromRef(v_a_1955_, v___x_1956_);
lean_dec(v_a_1955_);
v___x_1958_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1952_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_quotContext_x3f_1959_; 
lean_dec_ref_known(v___x_1958_, 1);
v_quotContext_x3f_1959_ = lean_ctor_get(v___y_1952_, 5);
if (lean_obj_tag(v_quotContext_x3f_1959_) == 0)
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_1953_);
lean_dec_ref(v___x_1960_);
v___y_1937_ = v_val_1951_;
v___y_1938_ = v___x_1957_;
goto v___jp_1936_;
}
else
{
v___y_1937_ = v_val_1951_;
v___y_1938_ = v___x_1957_;
goto v___jp_1936_;
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v___x_1957_);
lean_dec(v_val_1951_);
lean_del_object(v___x_1916_);
lean_dec(v_snd_1914_);
lean_dec(v_fst_1913_);
lean_dec(v_stx_1906_);
lean_dec_ref(v_modifiers_1905_);
v_a_1961_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1958_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1958_);
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
lean_dec(v_val_1951_);
lean_del_object(v___x_1916_);
lean_dec(v_snd_1914_);
lean_dec(v_fst_1913_);
lean_dec(v_stx_1906_);
lean_dec_ref(v_modifiers_1905_);
v_a_1969_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1954_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1954_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___boxed(lean_object* v_modifiers_2045_, lean_object* v_stx_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_Elab_Command_mkDefViewOfOpaque(v_modifiers_2045_, v_stx_2046_, v_a_2047_, v_a_2048_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object* v_modifiers_2063_, lean_object* v_stx_2064_){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v_docString_x3f_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v_id_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2065_ = lean_unsigned_to_nat(1u);
v___x_2066_ = l_Lean_Syntax_getArg(v_stx_2064_, v___x_2065_);
v___x_2067_ = l_Lean_Elab_expandOptDeclSig(v___x_2066_);
lean_dec(v___x_2066_);
v_fst_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_fst_2068_);
v_snd_2069_ = lean_ctor_get(v___x_2067_, 1);
lean_inc(v_snd_2069_);
lean_dec_ref(v___x_2067_);
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7));
v___x_2072_ = lean_box(2);
v___x_2073_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__0));
v_docString_x3f_2074_ = lean_ctor_get(v_modifiers_2063_, 1);
lean_inc(v_docString_x3f_2074_);
v___x_2075_ = l_Lean_Syntax_getArg(v_stx_2064_, v___x_2070_);
v___x_2076_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__2));
v___x_2077_ = 1;
v_id_2078_ = l_Lean_mkIdentFrom(v___x_2075_, v___x_2076_, v___x_2077_);
lean_dec(v___x_2075_);
v___x_2079_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfExample___closed__3));
v___x_2080_ = lean_unsigned_to_nat(2u);
v___x_2081_ = lean_mk_empty_array_with_capacity(v___x_2080_);
v___x_2082_ = lean_array_push(v___x_2081_, v_id_2078_);
v___x_2083_ = lean_array_push(v___x_2082_, v___x_2073_);
v___x_2084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2072_);
lean_ctor_set(v___x_2084_, 1, v___x_2079_);
lean_ctor_set(v___x_2084_, 2, v___x_2083_);
v___x_2085_ = 3;
v___x_2086_ = l_Lean_Syntax_getArgs(v_stx_2064_);
v___x_2087_ = l_Array_toSubarray___redArg(v___x_2086_, v___x_2070_, v___x_2080_);
v___x_2088_ = l_Subarray_copy___redArg(v___x_2087_);
v___x_2089_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2072_);
lean_ctor_set(v___x_2089_, 1, v___x_2071_);
lean_ctor_set(v___x_2089_, 2, v___x_2088_);
v___x_2090_ = l_Lean_Syntax_getArg(v_stx_2064_, v___x_2080_);
v___x_2091_ = lean_box(0);
v___x_2092_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2092_, 0, v_stx_2064_);
lean_ctor_set(v___x_2092_, 1, v___x_2089_);
lean_ctor_set(v___x_2092_, 2, v_modifiers_2063_);
lean_ctor_set(v___x_2092_, 3, v___x_2084_);
lean_ctor_set(v___x_2092_, 4, v_fst_2068_);
lean_ctor_set(v___x_2092_, 5, v_snd_2069_);
lean_ctor_set(v___x_2092_, 6, v___x_2090_);
lean_ctor_set(v___x_2092_, 7, v_docString_x3f_2074_);
lean_ctor_set(v___x_2092_, 8, v___x_2091_);
lean_ctor_set(v___x_2092_, 9, v___x_2091_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*10, v___x_2085_);
return v___x_2092_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_isDefLike(lean_object* v_stx_2128_){
_start:
{
lean_object* v_declKind_2129_; uint8_t v___y_2131_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v_declKind_2129_ = l_Lean_Syntax_getKind(v_stx_2128_);
v___x_2140_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__8));
v___x_2141_ = lean_name_eq(v_declKind_2129_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__10));
v___x_2143_ = lean_name_eq(v_declKind_2129_, v___x_2142_);
v___y_2131_ = v___x_2143_;
goto v___jp_2130_;
}
else
{
v___y_2131_ = v___x_2141_;
goto v___jp_2130_;
}
v___jp_2130_:
{
if (v___y_2131_ == 0)
{
lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2133_ = lean_name_eq(v_declKind_2129_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__3));
v___x_2135_ = lean_name_eq(v_declKind_2129_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__4));
v___x_2137_ = lean_name_eq(v_declKind_2129_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2139_ = lean_name_eq(v_declKind_2129_, v___x_2138_);
lean_dec(v_declKind_2129_);
return v___x_2139_;
}
else
{
lean_dec(v_declKind_2129_);
return v___x_2137_;
}
}
else
{
lean_dec(v_declKind_2129_);
return v___x_2135_;
}
}
else
{
lean_dec(v_declKind_2129_);
return v___x_2133_;
}
}
else
{
lean_dec(v_declKind_2129_);
return v___y_2131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object* v_stx_2144_){
_start:
{
uint8_t v_res_2145_; lean_object* v_r_2146_; 
v_res_2145_ = l_Lean_Elab_Command_isDefLike(v_stx_2144_);
v_r_2146_ = lean_box(v_res_2145_);
return v_r_2146_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefView___closed__1(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l_Lean_Elab_Command_mkDefView___closed__0));
v___x_2149_ = l_Lean_stringToMessageData(v___x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView(lean_object* v_modifiers_2150_, lean_object* v_stx_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_declKind_2155_; lean_object* v___x_2156_; 
lean_inc(v_stx_2151_);
v_declKind_2155_ = l_Lean_Syntax_getKind(v_stx_2151_);
v___x_2156_ = l_Lean_Elab_Command_getScope___redArg(v_a_2153_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2223_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2159_ = v___x_2156_;
v_isShared_2160_ = v_isSharedCheck_2223_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2156_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2223_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___y_2162_; lean_object* v_stx_2195_; lean_object* v_docString_x3f_2196_; uint8_t v_visibility_2197_; uint8_t v_isProtected_2198_; uint8_t v_computeKind_2199_; uint8_t v_recKind_2200_; uint8_t v_isUnsafe_2201_; lean_object* v_attrs_2202_; uint8_t v___y_2204_; uint8_t v___x_2220_; uint8_t v___x_2221_; 
v_stx_2195_ = lean_ctor_get(v_modifiers_2150_, 0);
v_docString_x3f_2196_ = lean_ctor_get(v_modifiers_2150_, 1);
v_visibility_2197_ = lean_ctor_get_uint8(v_modifiers_2150_, sizeof(void*)*3);
v_isProtected_2198_ = lean_ctor_get_uint8(v_modifiers_2150_, sizeof(void*)*3 + 1);
v_computeKind_2199_ = lean_ctor_get_uint8(v_modifiers_2150_, sizeof(void*)*3 + 2);
v_recKind_2200_ = lean_ctor_get_uint8(v_modifiers_2150_, sizeof(void*)*3 + 3);
v_isUnsafe_2201_ = lean_ctor_get_uint8(v_modifiers_2150_, sizeof(void*)*3 + 4);
v_attrs_2202_ = lean_ctor_get(v_modifiers_2150_, 2);
v___x_2220_ = 0;
v___x_2221_ = l_Lean_Elab_instBEqComputeKind_beq(v_computeKind_2199_, v___x_2220_);
if (v___x_2221_ == 0)
{
lean_dec(v_a_2157_);
v___y_2204_ = v___x_2221_;
goto v___jp_2203_;
}
else
{
uint8_t v_isMeta_2222_; 
v_isMeta_2222_ = lean_ctor_get_uint8(v_a_2157_, sizeof(void*)*10 + 2);
lean_dec(v_a_2157_);
v___y_2204_ = v_isMeta_2222_;
goto v___jp_2203_;
}
v___jp_2161_:
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__8));
v___x_2164_ = lean_name_eq(v_declKind_2155_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__10));
v___x_2166_ = lean_name_eq(v_declKind_2155_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2168_ = lean_name_eq(v_declKind_2155_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__3));
v___x_2170_ = lean_name_eq(v_declKind_2155_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__4));
v___x_2172_ = lean_name_eq(v_declKind_2155_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2174_ = lean_name_eq(v_declKind_2155_, v___x_2173_);
lean_dec(v_declKind_2155_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec_ref(v___y_2162_);
lean_del_object(v___x_2159_);
lean_dec(v_stx_2151_);
v___x_2175_ = lean_obj_once(&l_Lean_Elab_Command_mkDefView___closed__1, &l_Lean_Elab_Command_mkDefView___closed__1_once, _init_l_Lean_Elab_Command_mkDefView___closed__1);
v___x_2176_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v___x_2175_, v_a_2152_, v_a_2153_);
return v___x_2176_;
}
else
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2177_ = l_Lean_Elab_Command_mkDefViewOfExample(v___y_2162_, v_stx_2151_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2177_);
v___x_2179_ = v___x_2159_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
else
{
lean_object* v___x_2181_; 
lean_del_object(v___x_2159_);
lean_dec(v_declKind_2155_);
v___x_2181_ = l_Lean_Elab_Command_mkDefViewOfInstance(v___y_2162_, v_stx_2151_, v_a_2152_, v_a_2153_);
return v___x_2181_;
}
}
else
{
lean_object* v___x_2182_; 
lean_del_object(v___x_2159_);
lean_dec(v_declKind_2155_);
v___x_2182_ = l_Lean_Elab_Command_mkDefViewOfOpaque(v___y_2162_, v_stx_2151_, v_a_2152_, v_a_2153_);
return v___x_2182_;
}
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
lean_dec(v_declKind_2155_);
v___x_2183_ = l_Lean_Elab_Command_mkDefViewOfTheorem(v___y_2162_, v_stx_2151_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2183_);
v___x_2185_ = v___x_2159_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
else
{
lean_object* v___x_2187_; lean_object* v___x_2189_; 
lean_dec(v_declKind_2155_);
v___x_2187_ = l_Lean_Elab_Command_mkDefViewOfDef(v___y_2162_, v_stx_2151_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2187_);
v___x_2189_ = v___x_2159_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2193_; 
lean_dec(v_declKind_2155_);
v___x_2191_ = l_Lean_Elab_Command_mkDefViewOfAbbrev(v___y_2162_, v_stx_2151_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2191_);
v___x_2193_ = v___x_2159_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
v___jp_2203_:
{
if (v___y_2204_ == 0)
{
v___y_2162_ = v_modifiers_2150_;
goto v___jp_2161_;
}
else
{
lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__1));
v___x_2206_ = lean_name_eq(v_declKind_2155_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_Elab_Command_isDefLike___closed__6));
v___x_2208_ = lean_name_eq(v_declKind_2155_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2216_; 
lean_inc_ref(v_attrs_2202_);
lean_inc(v_docString_x3f_2196_);
lean_inc(v_stx_2195_);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_modifiers_2150_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; lean_object* v_unused_2218_; lean_object* v_unused_2219_; 
v_unused_2217_ = lean_ctor_get(v_modifiers_2150_, 2);
lean_dec(v_unused_2217_);
v_unused_2218_ = lean_ctor_get(v_modifiers_2150_, 1);
lean_dec(v_unused_2218_);
v_unused_2219_ = lean_ctor_get(v_modifiers_2150_, 0);
lean_dec(v_unused_2219_);
v___x_2210_ = v_modifiers_2150_;
v_isShared_2211_ = v_isSharedCheck_2216_;
goto v_resetjp_2209_;
}
else
{
lean_dec(v_modifiers_2150_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2216_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
uint8_t v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = 1;
if (v_isShared_2211_ == 0)
{
v___x_2214_ = v___x_2210_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_stx_2195_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_docString_x3f_2196_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_attrs_2202_);
lean_ctor_set_uint8(v_reuseFailAlloc_2215_, sizeof(void*)*3, v_visibility_2197_);
lean_ctor_set_uint8(v_reuseFailAlloc_2215_, sizeof(void*)*3 + 1, v_isProtected_2198_);
lean_ctor_set_uint8(v_reuseFailAlloc_2215_, sizeof(void*)*3 + 3, v_recKind_2200_);
lean_ctor_set_uint8(v_reuseFailAlloc_2215_, sizeof(void*)*3 + 4, v_isUnsafe_2201_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_ctor_set_uint8(v___x_2214_, sizeof(void*)*3 + 2, v___x_2212_);
v___y_2162_ = v___x_2214_;
goto v___jp_2161_;
}
}
}
else
{
v___y_2162_ = v_modifiers_2150_;
goto v___jp_2161_;
}
}
else
{
v___y_2162_ = v_modifiers_2150_;
goto v___jp_2161_;
}
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_declKind_2155_);
lean_dec(v_stx_2151_);
lean_dec_ref(v_modifiers_2150_);
v_a_2224_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2156_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2156_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object* v_modifiers_2232_, lean_object* v_stx_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_Elab_Command_mkDefView(v_modifiers_2232_, v_stx_2233_, v_a_2234_, v_a_2235_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2299_; uint8_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2299_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2300_ = 0;
v___x_2301_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2302_ = l_Lean_registerTraceClass(v___x_2299_, v___x_2300_, v___x_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2____boxed(lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_();
return v_res_2304_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_unsigned_to_nat(2390142386u);
v___x_2306_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2307_ = l_Lean_Name_num___override(v___x_2306_, v___x_2305_);
return v___x_2307_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2309_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2310_ = l_Lean_Name_str___override(v___x_2309_, v___x_2308_);
return v___x_2310_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = ((lean_object*)(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_));
v___x_2312_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2313_ = l_Lean_Name_str___override(v___x_2312_, v___x_2311_);
return v___x_2313_;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_unsigned_to_nat(2u);
v___x_2315_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2316_ = l_Lean_Name_num___override(v___x_2315_, v___x_2314_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2318_ = ((lean_object*)(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6));
v___x_2319_ = 0;
v___x_2320_ = lean_obj_once(&l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_, &l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
v___x_2321_ = l_Lean_registerTraceClass(v___x_2318_, v___x_2319_, v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2____boxed(lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_();
return v_res_2323_;
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
